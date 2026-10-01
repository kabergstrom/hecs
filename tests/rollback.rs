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
            &[Vacated { archetype: arch as u32, slot, entity: e, despawned: true }]
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

    // Released after the window: slot and ID go back to the allocators.
    world.despawn(e).unwrap();
    unsafe {
        world.release_quarantine_nonsync(arch, slot);
        assert!(world.release_held_nonsync(e));
        assert!(!world.release_held_nonsync(e), "released once");
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
            &[Vacated { archetype: arch as u32, slot, entity: e, despawned: false }]
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
