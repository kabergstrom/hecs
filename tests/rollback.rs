//! Rollback support: held IDs, revives (in a tombstone, a free row or a fresh one), forwarding,
//! row generations, the always-dead slot.

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

fn marked_world() -> World {
    let mut world = World::new();
    world.set_rollback_marker(Some(<Net as Component>::STABLE_TYPE_ID));
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

fn cref_ptr(cref: &CRef<i32>) -> GCPtr {
    // CRef<T> is a transparent GCPtr.
    unsafe { core::mem::transmute_copy(cref) }
}

/// Write `e`'s `Net` and `i32` values into its (revived) row.
unsafe fn write_row(world: &World, e: Entity, net: u32, v: i32) {
    let ptr = i32_ptr(world, e);
    ptr.value_ptr().as_ptr().cast::<i32>().write(v);
    let net_ptr = ptr.sibling::<Net>().unwrap();
    net_ptr.value_ptr().as_ptr().cast::<Net>().write(Net(net));
}

#[test]
fn a_referenced_tombstone_survives_sweeps_and_revives_in_place() {
    let mut world = marked_world();
    let e = world.spawn((Net(1), 5_i32));
    let other = world.spawn((Net(2), 7_i32));
    let cref = world.new_cref::<i32>(e).unwrap();
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));

    world.despawn(e).unwrap();
    assert!(!world.contains(e));
    assert!(world.is_held(e));
    unsafe {
        assert_eq!(world.vacated_nonsync(), &[Vacated { archetype: arch as u32, slot, entity: e, row_gen: world.archetype_at(arch).unwrap().row_generation(slot) }]);
        world.drain_vacated_nonsync(1);
        assert!(world.vacated_nonsync().is_empty());
    }
    assert_eq!(world.len(), 1);
    assert_eq!(read_cref(&mut world, &cref), None);
    let gen = unsafe { world.archetype_at(arch).unwrap().row_generation(slot) };
    unsafe {
        // Referenced on every cycle (a CRef some root holds): kept, never reused.
        for _ in 0..2 {
            cref_ptr(&cref).mark_referenced();
            assert_eq!(hecs::gc::sweep(&world), 0);
        }
        let a = world.archetype_at(arch).unwrap();
        assert_eq!(a.vacancy(slot), Some(Vacancy::Tombstone));
        assert_eq!(a.row_generation(slot), gen, "never freed");
    }
    let fresh = world.spawn((Net(3), 9_i32));
    assert_ne!(fresh.id(), e.id(), "the ID is held");
    assert_ne!(slot_of(&world, i32_ptr(&world, fresh)), (arch, slot));

    // The caller writes the values; the row comes back with the old bits.
    unsafe {
        assert_eq!(world.revive_nonsync(e, arch, Some(slot)), Ok(slot));
        write_row(&world, e, 1, 5);
        assert_eq!(world.archetype_at(arch).unwrap().vacancy(slot), None);
    }
    assert!(world.contains(e));
    assert!(!world.is_held(e));
    assert_eq!(world.len(), 3);
    assert_eq!(*world.get::<&i32>(e).unwrap(), 5);
    assert_eq!(*world.get::<&Net>(e).unwrap(), Net(1));
    assert_eq!(read_cref(&mut world, &cref), Some(5), "the CRef resolves again");
    assert_eq!(world.query::<&Net>().iter().count(), 3);
    assert_eq!(*world.get::<&i32>(other).unwrap(), 7);

    // Released: the ID goes back to the allocator; the row is freed by the first sweep that
    // finds it unreferenced.
    world.despawn(e).unwrap();
    unsafe {
        let v = *world.vacated_nonsync().last().unwrap();
        assert!(world.release_vacated_nonsync(&v));
        assert!(!world.release_held_nonsync(e), "released once");
        assert_eq!(hecs::gc::sweep(&world), 1);
        assert_eq!(world.archetype_at(arch).unwrap().row_generation(slot), gen + 1);
    }
    assert!(!world.is_held(e));
    let reused = world.spawn((Net(4), 11_i32));
    assert_eq!(reused.id(), e.id());
    assert_ne!(reused, e, "generation bumped on release");
    assert_eq!(slot_of(&world, i32_ptr(&world, reused)), (arch, slot));
    cleanup(world);
}

#[test]
fn an_unreferenced_tombstone_is_freed_and_its_entity_revives_elsewhere() {
    let mut world = marked_world();
    let a = world.spawn((Net(1), 5_i32));
    let b = world.spawn((Net(2), 6_i32));
    let (arch, slot_a) = slot_of(&world, i32_ptr(&world, a));
    let (_, slot_b) = slot_of(&world, i32_ptr(&world, b));
    world.despawn(a).unwrap();
    world.despawn(b).unwrap();
    unsafe {
        assert_eq!(hecs::gc::sweep(&world), 2, "nothing keeps an unreferenced tombstone");
        let ar = world.archetype_at(arch).unwrap();
        assert_eq!(ar.vacancy(slot_a), Some(Vacancy::Free));
        assert_eq!(ar.row_generation(slot_a), 1);
    }
    assert!(world.is_held(a) && world.is_held(b));

    // A spawn takes one free row; A revives in the other (taken off the free list), B in a
    // fresh row past every allocated one.
    let c = world.spawn((Net(3), 7_i32));
    let (_, slot_c) = slot_of(&world, i32_ptr(&world, c));
    let free = if slot_c == slot_a { slot_b } else { slot_a };
    let allocated = world.archetype_at(arch).unwrap().allocated_values_sync();
    unsafe {
        assert_eq!(world.revive_nonsync(a, arch, Some(slot_c)), Err(ReviveError::SlotOccupied));
        assert_eq!(world.revive_nonsync(a, arch, Some(free)), Ok(free));
        write_row(&world, a, 1, 5);
        assert_eq!(world.revive_nonsync(b, arch, None), Ok(allocated));
        write_row(&world, b, 2, 6);
    }
    assert_eq!(*world.get::<&i32>(a).unwrap(), 5);
    assert_eq!(*world.get::<&i32>(b).unwrap(), 6);
    assert_eq!(*world.get::<&i32>(c).unwrap(), 7);
    assert_eq!(world.query::<&Net>().iter().count(), 3);
    // The free list stays consistent: the next spawns take fresh rows, none twice.
    let d = world.spawn((Net(4), 8_i32));
    let e = world.spawn((Net(5), 9_i32));
    let mut rows: Vec<_> = [a, b, c, d, e].iter().map(|&x| slot_of(&world, i32_ptr(&world, x)).1).collect();
    rows.sort_unstable();
    rows.dedup();
    assert_eq!(rows.len(), 5);
    cleanup(world);
}

#[test]
fn taken_free_rows_are_tombstones_until_revived_or_swept() {
    let mut world = marked_world();
    let es: Vec<Entity> = (0..6).map(|i| world.spawn((Net(i), i as i32))).collect();
    let (arch, _) = slot_of(&world, i32_ptr(&world, es[0]));
    let slots: Vec<u32> = es.iter().map(|&e| slot_of(&world, i32_ptr(&world, e)).1).collect();
    for &e in &es {
        world.despawn(e).unwrap();
    }
    unsafe {
        assert_eq!(hecs::gc::sweep(&world), 6);
        // Rows from the head, the middle and the tail of the free list, and one not free.
        let live = world.spawn((Net(9), 9_i32));
        let (_, live_slot) = slot_of(&world, i32_ptr(&world, live));
        let want: Vec<u32> = slots.iter().copied().filter(|&s| s != live_slot).step_by(2).collect();
        let mut asked = want.clone();
        asked.push(live_slot);
        asked.sort_unstable();
        assert_eq!(world.take_free_rows_nonsync(arch, &asked), want.len() as u32);
        let ar = world.archetype_at(arch).unwrap();
        for &s in &want {
            assert_eq!(ar.vacancy(s), Some(Vacancy::Tombstone));
        }
        // Unclaimed: the next sweep frees them again.
        assert_eq!(hecs::gc::sweep(&world), want.len() as u32);
        for &s in &want {
            assert_eq!(ar.vacancy(s), Some(Vacancy::Free));
        }
    }
    // Every free row is handed out once.
    let more: Vec<Entity> = (0..5).map(|i| world.spawn((Net(20 + i), 0_i32))).collect();
    let mut rows: Vec<u32> = more.iter().map(|&e| slot_of(&world, i32_ptr(&world, e)).1).collect();
    rows.sort_unstable();
    rows.dedup();
    assert_eq!(rows.len(), 5);
    cleanup(world);
}

#[test]
fn an_undone_move_forwards_the_row_it_leaves() {
    for old_row_referenced in [true, false] {
        let mut world = marked_world();
        let e = world.spawn((Net(1), 5_i32));
        let before = world.new_cref::<i32>(e).unwrap();
        let (arch, slot) = slot_of(&world, i32_ptr(&world, e));

        world.insert_one(e, true).unwrap();
        assert!(unsafe { world.vacated_nonsync() }.is_empty(), "moves journal nothing");
        let after = world.new_cref::<i32>(e).unwrap();
        assert_eq!(read_cref(&mut world, &before), Some(5), "forwarded");
        *world.get::<&mut i32>(e).unwrap() = 6;
        unsafe {
            if old_row_referenced {
                cref_ptr(&before).mark_referenced();
            }
            hecs::gc::sweep(&world);
            let vacancy = world.archetype_at(arch).unwrap().vacancy(slot);
            assert_eq!(vacancy, Some(if old_row_referenced { Vacancy::Tombstone } else { Vacancy::Free }));
        }

        // Undo the move: leave the new archetype holding the ID, revive the old row (or, freed,
        // a fresh one), and forward the new row there.
        unsafe {
            let (new_arch, new_slot) = world.unspawn_nonsync(e, true).unwrap();
            assert!(world.is_held(e));
            let place = if old_row_referenced { Some(slot) } else { None };
            let row = world.revive_nonsync(e, arch, place).unwrap();
            assert_eq!(row == slot, old_row_referenced);
            write_row(&world, e, 1, 5);
            // Revived in the row it left (`Moved` to the new row), the revive already pointed the
            // new row back; otherwise forwarding does: Net and i32, bool stays dead.
            let forwarded = if old_row_referenced { 0 } else { 2 };
            assert_eq!(world.forward_nonsync(new_arch, new_slot, e), Ok(forwarded));
        }
        assert_eq!(*world.get::<&i32>(e).unwrap(), 5);
        assert!(world.get::<&bool>(e).is_err());
        assert_eq!(read_cref(&mut world, &after), Some(5), "a CRef taken after the move follows the entity back");
        if old_row_referenced {
            assert_eq!(read_cref(&mut world, &before), Some(5));
        }
        unsafe { hecs::gc::sweep(&world) };
        assert_eq!(world.query::<&bool>().iter().count(), 0);
        cleanup(world);
    }
}

/// A row the entity left by a move, then died in the row it reached (references to both
/// kept): a revive in the first row points the second back at it; a revive elsewhere has both
/// forwarded through the first's `Moved` chain.
#[test]
fn rows_left_through_a_move_and_a_death_follow_the_revive() {
    for in_place in [true, false] {
        let mut world = marked_world();
        let e = world.spawn((Net(1), 5_i32));
        let before = world.new_cref::<i32>(e).unwrap();
        let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
        world.insert_one(e, true).unwrap();
        let after = world.new_cref::<i32>(e).unwrap();
        let (new_arch, new_slot) = slot_of(&world, i32_ptr(&world, e));
        world.despawn(e).unwrap();
        unsafe {
            cref_ptr(&before).mark_referenced();
            hecs::gc::sweep(&world);
            assert_eq!(world.archetype_at(arch).unwrap().vacancy(slot), Some(Vacancy::Tombstone));
            assert_eq!(world.archetype_at(new_arch).unwrap().vacancy(new_slot), Some(Vacancy::Tombstone));
            let row = world.revive_nonsync(e, arch, in_place.then_some(slot)).unwrap();
            write_row(&world, e, 1, 7);
            if !in_place {
                assert_ne!(row, slot);
                assert_eq!(world.forward_nonsync(arch, slot, e), Ok(2), "the chain's end: the row it died in");
            }
        }
        assert_eq!(read_cref(&mut world, &before), Some(7), "in place: {in_place}");
        assert_eq!(read_cref(&mut world, &after), Some(7), "in place: {in_place}");
        cleanup(world);
    }
}

#[test]
fn unmarked_archetypes_free_as_before() {
    let mut world = marked_world();
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
fn revive_refuses_occupied_rows_and_unheld_ids() {
    let mut world = marked_world();
    let e = world.spawn((Net(1), 5_i32));
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
    unsafe {
        assert_eq!(world.revive_nonsync(e, arch, Some(slot)), Err(ReviveError::NotHeld), "live");
        world.unspawn_nonsync(e, true).unwrap();
        let f = world.spawn((Net(2), 6_i32));
        world.despawn(f).unwrap();
        let g = world.spawn((Net(3), 7_i32));
        let (_, g_slot) = slot_of(&world, i32_ptr(&world, g));
        assert_eq!(world.revive_nonsync(e, arch, Some(g_slot)), Err(ReviveError::SlotOccupied));
        assert_eq!(world.revive_nonsync(e, arch, Some(99)), Err(ReviveError::NoSuchSlot));
        assert!(world.release_held_nonsync(e));
        assert_eq!(world.revive_nonsync(e, arch, Some(slot)), Err(ReviveError::NotHeld));
    }
    cleanup(world);
}

#[test]
fn vacated_values_are_poisoned_in_debug_builds() {
    let mut world = World::new();
    let e = world.spawn((Net(1), 0x1234_5678_i32));
    let moved = world.spawn((Net(2), 0x1111_i32));
    let p = i32_ptr(&world, e);
    let q = i32_ptr(&world, moved);
    hecs::gc::debug_poison_vacated(Some(0xa5));
    world.despawn(e).unwrap();
    world.insert_one(moved, true).unwrap();
    hecs::gc::debug_poison_vacated(None);
    let read = |ptr: GCPtr| unsafe { ptr.value_ptr().as_ptr().cast::<i32>().read() };
    if cfg!(debug_assertions) {
        assert_eq!(read(p), i32::from_ne_bytes([0xa5; 4]), "dropped");
        assert_eq!(read(q), i32::from_ne_bytes([0xa5; 4]), "moved out");
    }
    assert_eq!(*world.get::<&i32>(moved).unwrap(), 0x1111);
    unsafe { hecs::gc::sweep(&world) };
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
fn take_holds_and_journals_like_despawn() {
    let mut world = marked_world();
    let e = world.spawn((Net(1), 5_i32));
    let (arch, slot) = slot_of(&world, i32_ptr(&world, e));
    let mut other = World::new();
    let moved = other.spawn(world.take(e).unwrap());
    assert_eq!(*other.get::<&i32>(moved).unwrap(), 5);
    assert!(world.is_held(e));
    unsafe {
        assert_eq!(world.vacated_nonsync(), &[Vacated { archetype: arch as u32, slot, entity: e, row_gen: world.archetype_at(arch).unwrap().row_generation(slot) }]);
        world.revive_nonsync(e, arch, Some(slot)).unwrap();
        write_row(&world, e, 1, 9);
    }
    assert_eq!(*world.get::<&i32>(e).unwrap(), 9);
    // A dropped TakenEntity despawns, holding too.
    drop(world.take(e).unwrap());
    assert!(world.is_held(e));
    cleanup(world);
    cleanup(other);
}

#[test]
#[should_panic(expected = "rollback-marked archetype")]
fn spawn_at_replacing_a_marked_entity_panics() {
    let mut world = marked_world();
    let e = world.spawn((Net(1), 5_i32));
    world.spawn_at(e, (Net(2), 6_i32));
}

#[test]
#[should_panic(expected = "held entity ID")]
fn spawn_at_a_held_id_panics() {
    let mut world = marked_world();
    let e = world.spawn((Net(1), 5_i32));
    world.despawn(e).unwrap();
    world.spawn_at(e, (Net(2), 6_i32));
}

#[test]
fn clear_and_migrate_bump_the_history_epoch() {
    let mut world = marked_world();
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
