use bevy_reflect::{Reflect, TypeRegistry};
use hecs::*;
use rand::{thread_rng, Rng};
use std::io;

/*
 Simple simulation
 Spawn multiple entities. They have health, damage, position and other components.
 On every tick every entity/unit:
     1. Moves in random direction.
     2. Finds closest entity to itself.
     3. Fires at it and applies damage.
     4. Gets damaged by other entities firing at them.
     5. If health <= 0, the unit dies.
State of the simulation is displayed in the sconsole through println! functions.
*/

#[derive(Clone, Debug, Reflect)]
struct Position {
    x: i32,
    y: i32,
}

#[derive(Debug, Reflect)]
struct Health(i32);

#[derive(Debug, Reflect)]
struct Speed(i32);

#[derive(Debug, Reflect)]
struct Damage(i32);

#[derive(Debug, Reflect)]
struct KillCount(i32);

#[derive(Default, Debug, Reflect)]
struct TargetTrack {
    target: Option<CRef<Position>>,
}

fn manhattan_dist(x0: i32, x1: i32, y0: i32, y1: i32) -> i32 {
    let dx = (x0 - x1).abs();
    let dy = (y0 - y1).abs();
    dx + dy
}

fn batch_spawn_entities(world: &mut World, n: usize) {
    let mut rng = thread_rng();

    let to_spawn = (0..n).map(|_| {
        let pos = Position {
            x: rng.gen_range(-10..10),
            y: rng.gen_range(-10..10),
        };
        let s = Speed(rng.gen_range(1..5));
        let hp = Health(rng.gen_range(30..50));
        let dmg = Damage(rng.gen_range(1..10));
        let kc = KillCount(0);
        let tt = TargetTrack::default();

        (pos, s, hp, dmg, kc, tt)
    });

    world.spawn_batch(to_spawn);
    // We could instead call `world.spawn((pos, s, hp, dmg, kc))` for each entity, but `spawn_batch`
    // is faster.
}

fn system_integrate_motion(world: &mut World, query: &mut PreparedQuery<(&mut Position, &Speed)>) {
    let mut rng = thread_rng();

    for (id, (pos, s)) in query.query_mut(world) {
        let change = (rng.gen_range(-s.0..s.0), rng.gen_range(-s.0..s.0));
        pos.x += change.0;
        pos.y += change.1;
        println!("Unit {:?} moved to {:?}", id, pos);
    }
}

// In this system entities find the closest entity and fire at them
fn system_fire_at_closest(mut world: &mut World) {
    let mut ptr = None;
    for (id0, (pos0, dmg0, kc0, tt0)) in
        &mut world.query::<With<(&Position, &Damage, &mut KillCount, &mut TargetTrack), &Health>>()
    {
        // Find closest:
        // Nested queries are O(n^2) and you usually want to avoid that by using some sort of
        // spatial index like a quadtree or more general BVH, which we don't bother with here since
        // it's out of scope for the example.
        let closest = world
            .query::<With<&Position, &Health>>()
            .iter()
            .filter(|(id1, _)| *id1 != id0)
            .min_by_key(|(_, pos1)| manhattan_dist(pos0.x, pos1.x, pos0.y, pos1.y))
            .map(|(entity, _pos)| entity);

        let closest = match closest {
            Some(entity) => entity,
            None => {
                println!("{:?} is the last survivor!", id0);
                return;
            }
        };

        let new_ref = world.new_cref::<Position>(closest).unwrap();
        if let Some(ptr) = &tt0.target {
            if !new_ref.ptr_eq(&ptr) {
                println!("new closest");
            }
        }
        ptr = Some(new_ref.clone());
        tt0.target = Some(new_ref);

        // Deal damage:
        /*
                // Get target unit hp like this:
                let mut hp1 = world.query_one::<&mut Health>(closest_id.unwrap()).unwrap();
                let hp1 = hp1.get().unwrap();
        */

        // Or like this:
        let mut hp1 = world.get::<&mut Health>(closest).unwrap();

        // Is target unit still alive?
        if hp1.0 > 0 {
            // apply damage
            hp1.0 -= dmg0.0;
            println!(
                "Unit {:?} was damaged by {:?} for {:?} HP",
                closest, id0, dmg0.0
            );
            if hp1.0 <= 0 {
                // if this killed it, increase own killcount
                kc0.0 += 1;
                println!("Unit {:?} was killed by unit {:?}!", closest, id0);
            }
        }
    }
    if let Some(ptr) = ptr {
        let gc_world = GCWorld::new(&mut world);

        println!("new {:?}", &*ptr.read());
        drop(gc_world);
    }
}

fn system_remove_dead(world: &mut World) {
    // Here we query entities with 0 or less hp and despawn them
    let mut to_remove: Vec<Entity> = Vec::new();
    for (id, hp) in &mut world.query::<&Health>() {
        if hp.0 <= 0 {
            to_remove.push(id);
        }
    }

    for entity in to_remove {
        world.despawn(entity).unwrap();
    }
}

fn print_world_state(world: &mut World) {
    println!("\nEntity stats:");
    for (id, (hp, pos, dmg, kc)) in &mut world.query::<(&Health, &Position, &Damage, &KillCount)>()
    {
        println!("ID: {:?}, {:?}, {:?}, {:?}, {:?}", id, hp, dmg, pos, kc);
    }
}

fn main() {
    let mut world = World::new();

    batch_spawn_entities(&mut world, 5);

    let mut motion_query = PreparedQuery::<(&mut Position, &Speed)>::default();

    loop {
        println!("\n'Enter' to continue simulation, '?' for entity list, 'q' to quit");

        let mut input = String::new();

        io::stdin().read_line(&mut input).unwrap();

        match input.trim() {
            "" => {
                // Run all simulation systems:
                system_integrate_motion(&mut world, &mut motion_query);
                system_fire_at_closest(&mut world);
                system_remove_dead(&mut world);
            }
            "q" => break,
            "?" => {
                print_world_state(&mut world);
            }
            _ => {}
        }
    }
    cleanup(world);
}

fn registry() -> TypeRegistry {
    let mut registry = TypeRegistry::new();
    registry.register::<Position>();
    registry.register::<Health>();
    registry.register::<Speed>();
    registry.register::<Damage>();
    registry.register::<KillCount>();
    registry
}

fn cleanup(mut world: World) {
    world.clear();
    unsafe { hecs::gc_trace(&registry(), &mut world, &[]) };
}
