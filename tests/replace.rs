use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use hecs::World;
use hecs::gc::GcWorld;

fn cleanup(mut world: World) {
    world.clear();
    unsafe { hecs::gc::sweep(&world) };
}

/// `insert` of a component the entity already has replaces it (hecs's
/// documented behaviour): the archetype doesn't change.
#[test]
fn insert_replaces_in_same_archetype() {
    let mut world = World::new();
    let e = world.spawn((123, "abc".to_string()));
    world.insert_one(e, 456).unwrap();
    assert_eq!(*world.get::<&i32>(e).unwrap(), 456);
    assert_eq!(*world.get::<&String>(e).unwrap(), "abc");
    assert_eq!(world.len(), 1);
    cleanup(world);
}

/// Replacing one and adding another (the entity moves archetype).
#[test]
fn insert_replaces_and_adds() {
    let mut world = World::new();
    let e = world.spawn((123, "abc".to_string()));
    world.insert(e, (456, true)).unwrap();
    assert_eq!(*world.get::<&i32>(e).unwrap(), 456);
    assert!(*world.get::<&bool>(e).unwrap());
    cleanup(world);
}

/// As across archetypes: a reference to the replaced value reads dead, one
/// to a retained component follows it to the entity's new row.
#[test]
fn insert_replace_crefs() {
    let mut world = World::new();
    let e = world.spawn((123_i32, "abc".to_string()));
    let old = world.new_cref::<i32>(e).unwrap();
    let kept = world.new_cref::<String>(e).unwrap();
    world.insert_one(e, 456_i32).unwrap();
    {
        let scope = GcWorld::new_scope(&mut world);
        assert!(old.try_read().is_none(), "the replaced value is dead");
        assert_eq!(*kept.read(), "abc");
        assert_eq!(kept.entity(), e);
        assert_eq!(*scope.get::<i32>(e).unwrap().read(), 456);
    }
    cleanup(world);
}

struct Counted(Arc<AtomicU32>);
impl Drop for Counted {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}
impl hecs::Component for Counted {
    const STABLE_TYPE_ID: hecs::StableTypeId = hecs::StableTypeId(hecs::StableTypeId::fnv1a(b"replace::Counted"));
    const TYPE_NAME: &'static str = "replace::Counted";
}

/// Replaced while borrowed (the engine inserts with `insert_nonsync` while
/// module code may hold a borrow): the old value is dropped once, at the
/// next sweep after the borrow ends; the new one is untouched.
#[test]
fn insert_replace_while_borrowed() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((Counted(drops.clone()), 1_u8));
    let old = world.new_cref::<Counted>(e).unwrap();
    {
        let scope = GcWorld::new_scope(&mut world);
        {
            let _borrow = old.read();
            scope.insert_one(e, Counted(drops.clone())).unwrap();
            assert_eq!(drops.load(Ordering::SeqCst), 0, "borrowed: not dropped yet");
        }
    }
    assert_eq!(drops.load(Ordering::SeqCst), 0, "pending dead until a sweep");
    unsafe { hecs::gc::sweep(&world) };
    assert_eq!(drops.load(Ordering::SeqCst), 1, "swept");
    assert!(world.get::<&Counted>(e).is_ok());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    cleanup(world);
    assert_eq!(drops.load(Ordering::SeqCst), 2);
}
