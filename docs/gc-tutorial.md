# hecs `gc` module — gamedev quick tutorial

## Why `GcWorld` exists

Vanilla ECS forces you into "systems": flat for-loops over component arrays, no entity referencing another entity directly. That's great for batch processing but painful for traditional gameplay code where a bullet wants to know its shooter, an AI wants to track its target, a UI element wants to mirror an enemy's HP.

`GcWorld` lets you write that style *without* fighting the borrow checker:

1. **Every world method takes `&self`** — `spawn`, `insert`, `remove`, `despawn`, `get`, `query`. Pass `&GcWorld` everywhere; no `&mut` plumbing.
2. **`CRef<T>` handles are first-class component data.** Store a `CRef<Position>` *inside* a `Bullet` component. Clone it, hand it to other entities, keep it on the player.
3. **Despawned components become tombstones, not freed memory.** Until you call `sweep()`, a `CRef` pointing at a despawned component is safe to call `try_read()` / `try_write()` on — they return `None`. Memory is only reclaimed by `sweep()`, and only for *unreferenced* tombstones (see the sweep section below).

Cost: single-threaded only (`!Send`), 256 active worlds globally, you must call `sweep()` periodically, and you are responsible for not letting `CRef`s to despawned entities outlive a `sweep()` (see [End-of-frame sweep](#end-of-frame-sweep)).

## Setup

```toml
[dependencies]
hecs = { git = "https://github.com/kabergstrom/hecs", branch = "gc", features = ["macros"] }
```

```rust
use hecs::{CRef, Component, GcWorld};

let world = GcWorld::new();
```

The `macros` feature enables `#[derive(Component)]`, which you need on every component type you store in the world.

## The one rule for `read()` / `write()`

**Always consume the guard on the line you call it.** Either inline the mutation, or copy the field out. Never bind it to a `let`.

```rust
// good — guard ends at the semicolon
pos.write().x += 1.0;
let hp = health.read().0;

// bad — guard lives until end of block, double-borrows on next call
let mut p = pos.write();
p.x += 1.0;
// ... later ...
pos.read();   // panic: already mutably borrowed
```

This rule alone eliminates 95% of the runtime borrow panics you'd otherwise hit.

## Building entities that reference each other

This is the pattern the `gc` module is built for. Components store `CRef`s to other entities' components.

```rust
#[derive(Component)] struct Pos { x: f32, y: f32 }
#[derive(Component)] struct Health(i32);

#[derive(Component)]
struct Enemy {
    target: CRef<Pos>,        // points at the player's Position
    speed: f32,
}

#[derive(Component)]
struct Bullet {
    shooter_hp: CRef<Health>, // points at whoever fired this bullet
    damage: i32,
}

let player = world.spawn((Pos { x: 0.0, y: 0.0 }, Health(100)));

// Enemy holds a handle directly to the player's Pos
let enemy = world.spawn((
    Pos { x: 50.0, y: 0.0 },
    Health(20),
    Enemy {
        target: world.get::<Pos>(player).unwrap(),
        speed: 2.0,
    },
));
```

The `Enemy` component now owns a direct handle to the player's position — no entity-id lookups, no per-frame `world.get()` calls. The handle is a raw pointer plus a slot index, not a reference count: cloning is cheap, and dropping a `CRef` does not free anything. Lifetime management happens at `sweep()` time (see below), not when the `CRef` is dropped.

## Per-entity behavior — traditional gamedev style

Put the logic on the component (or in a free function that takes the components). Call it on the entities you care about.

```rust
impl Enemy {
    fn step(&self, my_pos: &CRef<Pos>) {
        // chase the target — guard goes out of scope at the comma
        let dx = self.target.read().x - my_pos.read().x;
        let dy = self.target.read().y - my_pos.read().y;
        let len = (dx * dx + dy * dy).sqrt().max(0.0001);
        my_pos.write().x += self.speed * dx / len;
        my_pos.write().y += self.speed * dy / len;
    }
}

// Call it for one entity
let pos = world.get::<Pos>(enemy).unwrap();
let ai  = world.get::<Enemy>(enemy).unwrap();
ai.read().step(&pos);
```

If you want to "tick all enemies", a query is fine — but the loop body just delegates to per-entity logic, it isn't itself a "system":

```rust
for (_e, (pos, ai)) in world.query::<(&Pos, &Enemy)>().iter() {
    ai.read().step(&pos);
}
```

## Reacting to other entities mid-update

Because every `world.*` method is `&self`, an entity's update can spawn or despawn freely.

```rust
#[derive(Component)]
struct Gun {
    cooldown: f32,
    owner_pos: CRef<Pos>,
    owner_hp: CRef<Health>,
}

fn fire(world: &GcWorld, gun: &CRef<Gun>) {
    if gun.read().cooldown > 0.0 {
        gun.write().cooldown -= 1.0 / 60.0;
        return;
    }
    let (x, y) = (gun.read().owner_pos.read().x, gun.read().owner_pos.read().y);
    world.spawn((
        Pos { x, y },
        Bullet {
            shooter_hp: gun.read().owner_hp.clone(),  // clone the handle
            damage: 5,
        },
    ));
    gun.write().cooldown = 0.5;
}
```

Note `gun.read().owner_hp.clone()` — `CRef` is cheap to clone, that's the intended pattern for "hand a reference to something else."

## Despawning safely with stored handles

If the player dies, every `Enemy` still holds a `CRef<Pos>` pointing at the (now tombstoned) player slot. `try_read()` makes the cleanup natural:

```rust
impl Enemy {
    fn step(&self, my_pos: &CRef<Pos>) {
        let Some(target) = self.target.try_read() else {
            return;  // target is dead, just idle
        };
        let dx = target.x - my_pos.read().x;
        let dy = target.y - my_pos.read().y;
        // (note: `target` is bound here only because we destructured it from `Option`;
        //  drop it before any `write()` to the same component would matter)
        drop(target);
        let len = (dx * dx + dy * dy).sqrt().max(0.0001);
        my_pos.write().x += self.speed * dx / len;
        my_pos.write().y += self.speed * dy / len;
    }
}
```

This is the *only* place a `let`-bound guard is justified — when `Option`-destructuring, drop it explicitly before any conflicting access.

When a bullet's shooter is gone, do the same for `shooter_hp.try_read()`.

## End-of-frame sweep

`despawn()` only tombstones the entity's slots. Memory is reclaimed by `sweep()`:

```rust
fn end_of_frame(world: &mut hecs::World) {
    let freed = unsafe { hecs::gc::sweep(world) };
    let _ = freed;
}
```

### What sweep frees and what it doesn't

- **Alive slots are never freed by sweep.** As long as the entity hasn't been `despawn()`-ed, every `CRef` pointing at it stays valid across any number of sweeps. This is the common case — you can sweep freely.
- **Tombstoned slots (`Dead`, `Moved`) are freed by sweep.** A `CRef` whose target has been despawned is fine to call `try_read()` / `try_write()` on *before* the next sweep (they return `None`). After sweep, that slot is free and may be reused by a future `spawn()`, at which point the stale `CRef` would silently read whichever new component lands in the reused slot.

`CRef` is a raw pointer, not a refcount — holding one does not pin the slot. So the rule is:

> **Before each `sweep()`, drop (or replace) any stored `CRef`s whose target has been despawned.**

In practice this is one cleanup pass over the components that store `CRef`s:

```rust
for (_e, enemy) in world.query::<&mut Enemy>().iter() {
    if enemy.target.try_read().is_none() {
        // target was despawned; clear or replace before sweep
        // (here we just leave it; the type would need an Option<CRef<_>> for that)
    }
}
```

The "naturally degrades to `None`" idiom from earlier works *within* a frame. Across `sweep()`, you need to actually drop the dead handles, otherwise a future spawn into the same slot will make `try_read()` start returning the wrong component.

### `GcWorld::new()` vs. `new_scope`

If you used `GcWorld::new()` (standalone) you can't directly call `sweep` on it — `sweep` takes a `&World`. Use `GcWorld::new_scope(&mut world)` against a plain `World` you keep around for the sweep.

## Gotchas

- **Inline every `read()` / `write()`.** Bind only when destructuring `try_read()` / `try_write()`, and `drop()` before further access to that handle.
- **Don't hold a guard across `world.insert(...)` / `remove(...)` on the same entity.** Component storage may move; the guard becomes stale.
- **`CRef::write()` panics if already borrowed.** Use `try_write()` for re-entrant code.
- **`CRef` is not refcounted.** Dropping a `CRef` does nothing; cleanup happens at `sweep()`. Drop stale `CRef`s to despawned entities before sweeping (see above).
- **`GcWorld` is `!Send`.** Gameplay thread only. For parallel work, snapshot data first.
- **Never `mem::forget` a `GcWorldScope`.** It owns the swapped-in `World`; forgetting it leaks the world.
- **256 worlds max** globally — one per game session is fine.

## Minimal full example

```rust
use hecs::{CRef, Component, GcWorld};

#[derive(Component)] struct Pos { x: f32, y: f32 }
#[derive(Component)] struct Health(i32);
#[derive(Component)] struct Chaser { target: CRef<Pos>, speed: f32 }

fn main() {
    let world = GcWorld::new();

    let player = world.spawn((Pos { x: 0.0, y: 0.0 }, Health(100)));
    let enemy = world.spawn((
        Pos { x: 50.0, y: 50.0 },
        Chaser { target: world.get::<Pos>(player).unwrap(), speed: 1.0 },
    ));

    for _ in 0..30 {
        let pos = world.get::<Pos>(enemy).unwrap();
        let ai = world.get::<Chaser>(enemy).unwrap();
        let Some(t) = ai.read().target.try_read() else { continue };
        let (tx, ty) = (t.x, t.y);
        drop(t);
        let dx = tx - pos.read().x;
        let dy = ty - pos.read().y;
        let len = (dx * dx + dy * dy).sqrt().max(0.0001);
        pos.write().x += ai.read().speed * dx / len;
        pos.write().y += ai.read().speed * dy / len;
    }

    let pos = world.get::<Pos>(enemy).unwrap();
    println!("enemy at {}, {}", pos.read().x, pos.read().y);
}
```

The combination of `&self` mutation + `CRef`-as-component is what gives you the traditional "objects pointing at objects" feel without losing the cache-friendly storage of an ECS.
