//! Insert and remove refuse, changing nothing, when a component they would move is held by a
//! gc borrow guard (`CRef::read`/`write`).

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

use hecs::gc::GcWorld;
use hecs::{Component, ComponentError, Entity, StableTypeId, TakeError, World};

struct Counted(Arc<AtomicU32>);
impl Drop for Counted {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}
impl Component for Counted {
    const STABLE_TYPE_ID: StableTypeId = StableTypeId(StableTypeId::fnv1a(b"borrowed::Counted"));
    const TYPE_NAME: &'static str = "borrowed::Counted";
}

fn cleanup(mut world: World) {
    world.clear();
    unsafe { hecs::gc::sweep(&world) };
}

/// The entity is where it was, with every component intact and readable.
fn assert_intact(world: &mut World, e: Entity, n: i32, s: &str) {
    assert!(world.contains(e));
    assert_eq!(*world.get::<&i32>(e).unwrap(), n);
    assert_eq!(*world.get::<&String>(e).unwrap(), s);
    assert_eq!(world.len(), 1);
}

#[test]
fn insert_refused_while_a_kept_component_is_read() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string()));
    let kept = world.new_cref::<String>(e).unwrap();
    {
        let scope = GcWorld::new_scope(&mut world);
        let guard = kept.read();
        assert_eq!(
            scope.insert_one(e, Counted(drops.clone())),
            Err(ComponentError::Borrowed)
        );
        // The refused value was dropped once, by the caller's ownership, never put.
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(*guard, "abc");
        assert!(scope.get::<Counted>(e).is_err());
        drop(guard);
        // The guard is gone: the same insert now goes through.
        scope.insert_one(e, Counted(drops.clone())).unwrap();
        assert_eq!(*kept.read(), "abc");
        assert_eq!(kept.entity(), e);
    }
    assert_intact(&mut world, e, 1, "abc");
    assert!(world.get::<&Counted>(e).is_ok());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    cleanup(world);
    assert_eq!(drops.load(Ordering::SeqCst), 2);
}

#[test]
fn insert_refused_while_a_kept_component_is_written() {
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string()));
    let kept = world.new_cref::<i32>(e).unwrap();
    {
        let scope = GcWorld::new_scope(&mut world);
        let mut guard = kept.write();
        assert_eq!(scope.insert_one(e, true), Err(ComponentError::Borrowed));
        *guard = 2;
    }
    assert_intact(&mut world, e, 2, "abc");
    assert!(world.get::<&bool>(e).is_err());
    cleanup(world);
}

/// A guard can outlive its `GcWorld` scope; `&mut World` insert refuses too.
#[test]
fn insert_refused_through_mut_world_with_a_leaked_guard() {
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string()));
    let kept = world.new_cref::<String>(e).unwrap();
    let guard = {
        let _scope = GcWorld::new_scope(&mut world);
        kept.read()
    };
    assert_eq!(world.insert_one(e, true), Err(ComponentError::Borrowed));
    assert_eq!(*guard, "abc");
    drop(guard);
    assert_intact(&mut world, e, 1, "abc");
    world.insert_one(e, true).unwrap();
    assert!(*world.get::<&bool>(e).unwrap());
    cleanup(world);
}

#[test]
fn remove_refused_while_the_removed_component_is_read() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string(), Counted(drops.clone())));
    let removed = world.new_cref::<Counted>(e).unwrap();
    {
        let scope = GcWorld::new_scope(&mut world);
        let guard = removed.read();
        assert_eq!(
            scope.remove_one::<Counted>(e).err(),
            Some(ComponentError::Borrowed)
        );
        assert!(Arc::ptr_eq(&guard.0, &drops));
        drop(guard);
        assert!(scope.get::<Counted>(e).is_ok());
    }
    assert_intact(&mut world, e, 1, "abc");
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    let taken = world.remove_one::<Counted>(e).unwrap();
    drop(taken);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_intact(&mut world, e, 1, "abc");
    cleanup(world);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn remove_refused_while_a_kept_component_is_read() {
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string(), true));
    let kept = world.new_cref::<String>(e).unwrap();
    let guard = {
        let scope = GcWorld::new_scope(&mut world);
        let guard = kept.read();
        assert_eq!(scope.remove_one::<bool>(e), Err(ComponentError::Borrowed));
        guard
    };
    assert_eq!(world.remove_one::<bool>(e), Err(ComponentError::Borrowed));
    drop(guard);
    assert_intact(&mut world, e, 1, "abc");
    assert!(*world.get::<&bool>(e).unwrap());
    assert_eq!(world.remove_one::<bool>(e), Ok(true));
    assert_intact(&mut world, e, 1, "abc");
    cleanup(world);
}

/// A missing component refuses before any is taken (it used to tombstone the ones before it).
#[test]
fn remove_with_a_missing_component_takes_nothing() {
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string()));
    assert!(matches!(
        world.remove::<(i32, bool)>(e),
        Err(ComponentError::MissingComponent(_))
    ));
    assert_intact(&mut world, e, 1, "abc");
    cleanup(world);
}

#[test]
fn remove_by_ids_refused_while_a_kept_component_is_read() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string(), Counted(drops.clone())));
    let kept = world.new_cref::<String>(e).unwrap();
    let guard = {
        let _scope = GcWorld::new_scope(&mut world);
        kept.read()
    };
    let ids = [<Counted as Component>::STABLE_TYPE_ID];
    assert_eq!(
        unsafe { world.remove_by_ids_nonsync(e, &ids) },
        Err(ComponentError::Borrowed)
    );
    assert_eq!(drops.load(Ordering::SeqCst), 0, "nothing dropped");
    drop(guard);
    assert_intact(&mut world, e, 1, "abc");
    assert!(world.get::<&Counted>(e).is_ok());
    // An id the entity lacks is refused too, before anything is dropped.
    let wrong = [ids[0], <bool as Component>::STABLE_TYPE_ID];
    assert!(matches!(
        unsafe { world.remove_by_ids_nonsync(e, &wrong) },
        Err(ComponentError::MissingComponent(_))
    ));
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    // A repeated id removes once.
    unsafe { world.remove_by_ids_nonsync(e, &[ids[0], ids[0]]) }.unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert!(world.get::<&Counted>(e).is_err());
    assert_intact(&mut world, e, 1, "abc");
    cleanup(world);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

/// Removing a borrowed component by id is allowed: it is dropped once the guard goes.
#[test]
fn remove_by_ids_of_a_read_component_defers_its_drop() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string(), Counted(drops.clone())));
    let removed = world.new_cref::<Counted>(e).unwrap();
    // `GcWorld` has no by-id remove: take a guard that outlives its scope instead.
    let guard = {
        let _scope = GcWorld::new_scope(&mut world);
        removed.read()
    };
    let ids = [<Counted as Component>::STABLE_TYPE_ID];
    unsafe { world.remove_by_ids_nonsync(e, &ids) }.unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 0, "borrowed: pending dead");
    assert!(Arc::ptr_eq(&guard.0, &drops), "the guard still reads the value");
    drop(guard);
    assert_intact(&mut world, e, 1, "abc");
    assert!(world.get::<&Counted>(e).is_err());
    unsafe { hecs::gc::sweep(&world) };
    assert_eq!(drops.load(Ordering::SeqCst), 1, "swept");
    cleanup(world);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn take_refused_while_a_component_is_read() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string(), Counted(drops.clone())));
    let kept = world.new_cref::<String>(e).unwrap();
    let guard = {
        let _scope = GcWorld::new_scope(&mut world);
        kept.read()
    };
    assert_eq!(world.take(e).err(), Some(TakeError::Borrowed));
    assert_eq!(*guard, "abc");
    drop(guard);
    assert_intact(&mut world, e, 1, "abc");
    assert!(world.get::<&Counted>(e).is_ok());
    assert_eq!(drops.load(Ordering::SeqCst), 0, "nothing dropped");
    assert_eq!(kept.entity(), e);
    cleanup(world);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn take_refused_while_a_component_is_written() {
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string()));
    let kept = world.new_cref::<i32>(e).unwrap();
    let mut guard = {
        let _scope = GcWorld::new_scope(&mut world);
        kept.write()
    };
    assert_eq!(world.take(e).err(), Some(TakeError::Borrowed));
    *guard = 2;
    drop(guard);
    assert_intact(&mut world, e, 2, "abc");
    cleanup(world);
}

#[test]
fn take_without_borrows_moves_the_entity() {
    let drops = Arc::new(AtomicU32::new(0));
    let mut world = World::new();
    let e = world.spawn((1_i32, "abc".to_string(), Counted(drops.clone())));
    let mut other = World::new();
    let moved = other.spawn(world.take(e).unwrap());
    assert!(!world.contains(e));
    assert_eq!(world.len(), 0);
    assert_intact(&mut other, moved, 1, "abc");
    assert_eq!(drops.load(Ordering::SeqCst), 0, "moved, not dropped");
    assert_eq!(world.take(e).err(), Some(TakeError::NoSuchEntity));
    cleanup(world);
    cleanup(other);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}
