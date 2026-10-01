//! Rollback support: slot quarantine, held IDs, in-place revive, the always-dead slot.

use hecs::gc::GCPtr;
use hecs::*;

#[derive(Debug, Clone, Copy, PartialEq)]
struct Net(u32);
impl Component for Net {
    const STABLE_TYPE_ID: StableTypeId = StableTypeId(StableTypeId::fnv1a(b"rollback::Net"));
}

fn cleanup(mut world: World) {
    world.clear();
    unsafe { hecs::gc::sweep(&world) };
}

fn quarantining_world() -> World {
    let mut world = World::new();
    world.set_quarantine_marker(Some(<Net as Component>::STABLE_TYPE_ID));
    world
}

/// `(archetype index, slot)` of the slot `ptr` points into.
fn slot_of(world: &World, ptr: GCPtr) -> (usize, u32) {
    let arch = ptr.archetype();
    let index = (0..world.archetype_count())
        .find(|&i| core::ptr::eq(world.archetype_at(i).unwrap(), arch))
        .expect("archetype of the pointer");
    (index, ptr.archetype_slot())
}

fn i32_ptr(world: &World, e: Entity) -> GCPtr {
    world
        .get_gc_ptr_by_id(e, <i32 as Component>::STABLE_TYPE_ID)
        .unwrap()
}

fn read_cref(world: &mut World, cref: &CRef<i32>) -> Option<i32> {
    let _scope = GcWorld::new_scope(world);
    cref.try_read().map(|v| *v)
}

#[test]
fn despawned_entity_revives_in_place_with_its_bits() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    let other = world.spawn((Net(2), 7_i32));
    let cref = world.new_cref::<i32>(e).unwrap();
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));

    world.despawn(e).unwrap();
    assert!(!world.contains(e));
    assert!(world.is_held(e));
    unsafe {
        assert_eq!(
            world.vacated_nonsync(),
            &[Vacated { archetype: arch as u32, slot, entity: e, kind: VacateKind::Despawned }]
        );
        world.drain_vacated_nonsync(1);
        assert!(world.vacated_nonsync().is_empty());
    }
    assert_eq!(world.len(), 1);
    assert_eq!(read_cref(&mut world, &cref), None);
    unsafe {
        hecs::gc::sweep(&world);
        hecs::gc::sweep(&world);
        assert!(world.archetype_at(arch).unwrap().is_quarantined(slot));
    }
    // Neither the slot nor the ID is reused while quarantined.
    let fresh = world.spawn((Net(3), 9_i32));
    assert_ne!(fresh.id(), e.id());
    assert_ne!(slot_of(&world, i32_ptr(&world, fresh)), (arch, slot));

    // The caller restores the value bytes; the slot comes back with the old bits.
    let ptr = cref_ptr(&cref);
    unsafe {
        world.revive_nonsync(e, arch, slot).unwrap();
        ptr.value_ptr().as_ptr().cast::<i32>().write(5);
        let net = ptr.sibling::<Net>().unwrap();
        net.value_ptr().as_ptr().cast::<Net>().write(Net(1));
        assert!(!world.archetype_at(arch).unwrap().is_quarantined(slot));
    }
    assert!(world.contains(e));
    assert!(!world.is_held(e));
    assert_eq!(world.len(), 3);
    assert_eq!(*world.get::<&i32>(e).unwrap(), 5);
    assert_eq!(*world.get::<&Net>(e).unwrap(), Net(1));
    assert_eq!(read_cref(&mut world, &cref), Some(5));
    assert_eq!(world.query::<&Net>().iter().count(), 3);
    assert_eq!(*world.get::<&i32>(other).unwrap(), 7);

    // Released after the window: the ID goes back to the allocator, the slot after one more
    // window (history may still point at it).
    world.despawn(e).unwrap();
    unsafe {
        let v = *world.vacated_nonsync().last().unwrap();
        world.release_vacated_nonsync(&v);
        assert!(!world.release_held_nonsync(e), "released once");
        assert_eq!(hecs::gc::sweep(&world), 0);
        let swept = *world.vacated_nonsync().last().unwrap();
        assert_eq!(swept, Vacated { archetype: arch as u32, slot, entity: Entity::DANGLING, kind: VacateKind::Swept });
        world.release_vacated_nonsync(&swept);
        assert_eq!(hecs::gc::sweep(&world), 1);
    }
    assert!(!world.is_held(e));
    let reused = world.spawn((Net(4), 11_i32));
    assert_eq!(reused.id(), e.id());
    assert_ne!(reused, e, "generation bumped on release");
    assert_eq!(slot_of(&world, i32_ptr(&world, reused)), (arch, slot));
    assert_eq!(read_cref(&mut world, &cref), Some(11), "the stale CRef sees the slot's new owner");
    cleanup(world);
}

fn cref_ptr(cref: &CRef<i32>) -> GCPtr {
    // CRef<T> is a transparent GCPtr.
    unsafe { core::mem::transmute_copy(cref) }
}

#[test]
fn moved_out_slot_is_quarantined_and_a_move_can_be_undone() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    let cref = world.new_cref::<i32>(e).unwrap();
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));

    world.insert_one(e, true).unwrap();
    unsafe {
        assert_eq!(
            world.vacated_nonsync(),
            &[Vacated { archetype: arch as u32, slot, entity: e, kind: VacateKind::Moved }]
        );
        // Unreferenced, yet the Moved forwarding survives the sweep.
        hecs::gc::sweep(&world);
        assert!(world.archetype_at(arch).unwrap().is_quarantined(slot));
    }
    assert_eq!(read_cref(&mut world, &cref), Some(5));
    *world.get::<&mut i32>(e).unwrap() = 6;

    // Undo the move: leave the new archetype holding the ID, revive the old slot.
    unsafe {
        world.despawn_unquarantined_nonsync(e, true).unwrap();
        assert!(world.is_held(e));
        world.revive_nonsync(e, arch, slot).unwrap();
        cref_ptr(&cref).value_ptr().as_ptr().cast::<i32>().write(5);
    }
    assert_eq!(*world.get::<&i32>(e).unwrap(), 5);
    assert!(world.get::<&bool>(e).is_err());
    assert_eq!(read_cref(&mut world, &cref), Some(5));
    unsafe { hecs::gc::sweep(&world) };
    assert_eq!(world.query::<&bool>().iter().count(), 0);
    cleanup(world);
}

#[test]
fn removing_a_component_quarantines_the_old_slot() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32, true));
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
    world.remove_one::<bool>(e).unwrap();
    unsafe {
        hecs::gc::sweep(&world);
        assert!(world.archetype_at(arch).unwrap().is_quarantined(slot));
        world.remove_by_ids_nonsync(e, &[<i32 as Component>::STABLE_TYPE_ID]).unwrap();
        let (arch2, slot2) = slot_of(&world, world.get_gc_ptr_by_id(e, <Net as Component>::STABLE_TYPE_ID).unwrap());
        assert_ne!(arch2, arch);
        // Leaving the marker's archetypes: the slot left behind is still a marked one.
        world.remove_one::<Net>(e).unwrap();
        assert!(world.archetype_at(arch2).unwrap().is_quarantined(slot2));
        world.release_quarantine_nonsync(arch, slot);
        world.release_quarantine_nonsync(arch2, slot2);
    }
    cleanup(world);
}

#[test]
fn unmarked_archetypes_free_as_before() {
    let mut world = quarantining_world();
    let e = world.spawn((5_i32,));
    world.despawn(e).unwrap();
    assert!(!world.is_held(e));
    assert!(unsafe { world.vacated_nonsync() }.is_empty(), "unmarked archetypes keep no journal");
    assert_eq!(unsafe { hecs::gc::sweep(&world) }, 1);
    let f = world.spawn((6_i32,));
    assert_eq!(f.id(), e.id());
    cleanup(world);
}

#[test]
fn revive_refuses_occupied_slots_and_unheld_ids() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
    unsafe {
        assert_eq!(world.revive_nonsync(e, arch, slot), Err(ReviveError::SlotOccupied));
        assert_eq!(world.revive_nonsync(e, arch, 99), Err(ReviveError::NoSuchSlot));
        world.despawn_unquarantined_nonsync(e, false).unwrap();
        assert_eq!(world.revive_nonsync(e, arch, slot), Err(ReviveError::NotHeld));
    }
    cleanup(world);
}

#[test]
fn dead_slot_never_resolves() {
    let mut world = World::new();
    let e = world.spawn((5_i32,));
    let dead = world.dead_cref::<i32>();
    let mut ptr = world.dead_gc_ptr();
    assert_eq!(ptr, cref_ptr(&dead), "one canonical slot per world");
    unsafe {
        assert_eq!(world.entity_from_gc_ptr(ptr), None);
        assert!(!ptr.header_ptr().as_ref().is_alive());
        ptr.mark_referenced();
        hecs::gc::sweep(&world);
    }
    assert_eq!(read_cref(&mut world, &dead), None);
    assert_eq!(world.query::<()>().iter().count(), 1);
    assert_eq!(*world.get::<&i32>(e).unwrap(), 5);
    let other = World::new();
    assert_ne!(other.dead_gc_ptr(), ptr);
    cleanup(world);
}

#[test]
fn data_accessors_walk_raw_slots() {
    let mut world = World::new();
    let es: Vec<Entity> = (0..3000).map(|i| world.spawn((i as u64,))).collect();
    let arch = (0..world.archetype_count())
        .map(|i| world.archetype_at(i).unwrap())
        .find(|a| a.has::<u64>())
        .unwrap();
    let col = arch.column_index(<u64 as Component>::STABLE_TYPE_ID).unwrap();
    let data = unsafe { arch.get_data_storage(col) };
    assert!(data.chunks().len() >= 2, "spans chunks");
    for (i, &e) in es.iter().enumerate() {
        let slot = i as u32;
        let chunk = data.chunks()[i / data.entities_per_chunk()];
        let manual = unsafe {
            chunk.add(data.data_start() + (i % data.entities_per_chunk()) * data.stride())
        };
        assert_eq!(manual, unsafe { data.slot_ptr(slot) });
        let value = unsafe { manual.add(data.value_start()).cast::<u64>().read() };
        assert_eq!(value, i as u64);
        assert_eq!(arch.entity(slot), e);
    }
    cleanup(world);
}

#[test]
fn swept_slots_wait_for_release_and_rearm_when_referenced_again() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    let cref = world.new_cref::<i32>(e).unwrap();
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
    world.despawn(e).unwrap();
    unsafe {
        let v = world.vacated_nonsync()[0];
        world.drain_vacated_nonsync(1);
        world.release_vacated_nonsync(&v);
        // Unreferenced: deferred, not freed.
        assert_eq!(hecs::gc::sweep(&world), 0);
        let swept = world.vacated_nonsync()[0];
        assert_eq!(swept.kind, VacateKind::Swept);
        world.drain_vacated_nonsync(1);
        assert!(world.archetype_at(arch).unwrap().is_quarantined(slot));
        assert_eq!(hecs::gc::sweep(&world), 0, "quarantined until released");
        let other = world.spawn((Net(2), 6_i32));
        assert_ne!(slot_of(&world, i32_ptr(&world, other)), (arch, slot));

        // Released, but live memory points at it again (a restored history copy): kept, and
        // once unreferenced it is deferred anew.
        world.release_vacated_nonsync(&swept);
        cref_ptr(&cref).mark_referenced();
        assert_eq!(hecs::gc::sweep(&world), 0);
        assert!(world.vacated_nonsync().is_empty());
        assert_eq!(hecs::gc::sweep(&world), 0);
        let again = world.vacated_nonsync()[0];
        assert_eq!((again.slot, again.kind), (slot, VacateKind::Swept));
        world.drain_vacated_nonsync(1);
        world.release_vacated_nonsync(&again);
        assert_eq!(hecs::gc::sweep(&world), 1);
    }
    let reused = world.spawn((Net(3), 7_i32));
    assert_eq!(slot_of(&world, i32_ptr(&world, reused)), (arch, slot));
    cleanup(world);
}

#[test]
fn take_holds_and_journals_like_despawn() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
    let mut other = World::new();
    let moved = other.spawn(world.take(e).unwrap());
    assert_eq!(*other.get::<&i32>(moved).unwrap(), 5);
    assert!(world.is_held(e));
    unsafe {
        assert_eq!(
            world.vacated_nonsync(),
            &[Vacated { archetype: arch as u32, slot, entity: e, kind: VacateKind::Despawned }]
        );
        world.revive_nonsync(e, arch, slot).unwrap();
        let ptr = i32_ptr(&world, e);
        ptr.value_ptr().as_ptr().cast::<i32>().write(9);
    }
    assert_eq!(*world.get::<&i32>(e).unwrap(), 9);
    // A dropped TakenEntity despawns, holding too.
    drop(world.take(e).unwrap());
    assert!(world.is_held(e));
    cleanup(world);
    cleanup(other);
}

#[test]
#[should_panic(expected = "quarantining archetype")]
fn spawn_at_replacing_a_quarantined_entity_panics() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    world.spawn_at(e, (Net(2), 6_i32));
}

#[test]
#[should_panic(expected = "held entity ID")]
fn spawn_at_a_held_id_panics() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    world.despawn(e).unwrap();
    world.spawn_at(e, (Net(2), 6_i32));
}

#[test]
fn clear_and_migrate_bump_the_history_epoch() {
    let mut world = quarantining_world();
    let e = world.spawn((Net(1), 5_i32));
    world.despawn(e).unwrap();
    let epoch = world.history_epoch();
    world.clear();
    assert_ne!(world.history_epoch(), epoch);
    assert!(unsafe { world.vacated_nonsync() }.is_empty());
    assert!(!world.is_held(e));
    let epoch = world.history_epoch();
    world.spawn((Net(1), 5_i32));
    world.migrate_components(&[TypeInfo::of::<i32>()], |_, old, new| unsafe {
        new.cast::<i32>().write(old.cast::<i32>().read())
    });
    assert_ne!(world.history_epoch(), epoch);
    cleanup(world);
}
