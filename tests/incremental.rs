//! The incremental GC's world side (`gc::incr`) on the dense header words: an armed cell's
//! first exclusive borrow greys it once and lands disarmed, reads keep the arm, conflicts stay
//! conflicts; new cells of traced columns are greyed during a cycle (unarmed), others are not;
//! tombstones written during a cycle are marked, so that cycle's sweep keeps them.

use hecs::gc::header::Arm;
use hecs::gc::{incr, GCPtr, GcWorld};
use hecs::{Component, Entity, StableTypeId, World};

fn ptr<T: Component>(world: &World, e: Entity) -> GCPtr {
    world.get_gc_ptr_by_id(e, T::STABLE_TYPE_ID).unwrap()
}

fn flag(p: GCPtr) -> i32 {
    unsafe { p.header_ptr().as_ref() }.borrow_flag()
}

fn arm(p: GCPtr) -> Arm {
    unsafe { p.header_ptr().as_ref() }.arm()
}

fn armed(p: GCPtr) -> bool {
    unsafe { p.header_ptr().as_ref() }.is_slot_armed()
}

fn greyed(world: &World) -> (Vec<GCPtr>, incr::GreyCounts) {
    let mut out = Vec::new();
    let counts = incr::take_grey(world.gc_world_slot(), &mut out);
    (out, counts)
}

fn cleanup(mut world: World) {
    incr::end_cycle(world.gc_world_slot());
    world.clear();
    unsafe { hecs::gc::sweep(&world) };
}

#[derive(Debug, PartialEq)]
struct Pair(i32, i32);
impl Component for Pair {
    const STABLE_TYPE_ID: StableTypeId = StableTypeId(StableTypeId::fnv1a(b"incremental::Pair"));
    const TYPE_NAME: &'static str = "incremental::Pair";
}

#[derive(Debug, PartialEq)]
struct Tag(u8);
impl Component for Tag {
    const STABLE_TYPE_ID: StableTypeId = StableTypeId(StableTypeId::fnv1a(b"incremental::Tag"));
    const TYPE_NAME: &'static str = "incremental::Tag";
}

#[test]
fn an_armed_write_greys_once_and_reads_keep_the_arm() {
    let mut world = World::new();
    let e = world.spawn((1_i32,));
    let cref = world.new_cref::<i32>(e).unwrap();
    let p = ptr::<i32>(&world, e);
    incr::begin_cycle(&world, &[<i32 as Component>::STABLE_TYPE_ID]);
    {
        let _scope = GcWorld::new_scope(&mut world);
        // Unarmed: no grey.
        let w = cref.write();
        assert_eq!(flag(p), -2);
        assert!(cref.try_read().is_none(), "a reader under a writer");
        assert!(cref.try_write().is_none(), "a second writer");
        drop(w);
        assert_eq!(flag(p), 0);
        // Armed: the first write greys and disarms; the release lands on 0.
        assert_eq!(arm(p), Arm::Armed);
        assert_eq!(flag(p), 1);
        let w = cref.write();
        assert_eq!(flag(p), -2);
        assert!(cref.try_read().is_none(), "a reader under a writer of an armed cell");
        drop(w);
        assert_eq!(flag(p), 0, "disarmed: the cell is grey");
        // Reads of an armed cell pass and keep the arm.
        assert_eq!(arm(p), Arm::Armed);
        let r = cref.read();
        assert_eq!(flag(p), 3);
        let r2 = cref.read();
        assert_eq!(flag(p), 5);
        assert!(cref.try_write().is_none(), "armed with readers: a conflict, not the cold path");
        drop((r, r2));
        assert_eq!(flag(p), 1);
    }
    let (cells, counts) = greyed(&world);
    assert_eq!(cells, vec![p], "one grey, for the first armed write only");
    assert_eq!(counts, incr::GreyCounts { written: 1, new: 0 });
    // The raw-write barrier: once.
    unsafe {
        p.barrier();
        p.barrier();
    }
    assert!(!armed(p));
    assert_eq!(greyed(&world).0, vec![p]);
    cleanup(world);
}

#[test]
fn split_writers_of_an_armed_cell_grey_once() {
    let mut world = World::new();
    let e = world.spawn((Pair(1, 2),));
    let cref = world.new_cref::<Pair>(e).unwrap();
    let p = ptr::<Pair>(&world, e);
    incr::begin_cycle(&world, &[Pair::STABLE_TYPE_ID]);
    {
        let _scope = GcWorld::new_scope(&mut world);
        arm(p);
        let w = cref.write();
        let (mut a, mut b) = hecs::gc::RefMut::map_split(w, |v| (&mut v.0, &mut v.1));
        assert_eq!(flag(p), -4);
        assert!(cref.try_read().is_none());
        assert_eq!(arm(p), Arm::WriteBorrowed, "a writer is never armed");
        assert_eq!(unsafe { p.header_ptr().as_ref() }.readable(), Some(false));
        *a = 3;
        *b = 4;
        drop(a);
        assert_eq!(flag(p), -2);
        drop(b);
        assert_eq!(flag(p), 0);
        assert_eq!(*cref.read(), Pair(3, 4));
    }
    assert_eq!(greyed(&world).0, vec![p]);
    cleanup(world);
}

#[test]
fn outside_a_cycle_nothing_is_greyed() {
    let mut world = World::new();
    let e = world.spawn((1_i32,));
    let p = ptr::<i32>(&world, e);
    arm(p);
    let hooked = hecs::gc::armed_writes();
    unsafe { p.barrier() };
    assert_eq!(hecs::gc::armed_writes(), hooked + 1, "the hook is reached");
    world.spawn((2_i32,));
    assert!(greyed(&world).0.is_empty(), "but nothing is pushed");
    assert!(!incr::cycle_active(world.gc_world_slot()));
    cleanup(world);
}

#[test]
fn a_cycle_greys_new_cells_of_traced_columns_and_keeps_its_tombstones() {
    let mut world = World::new();
    let before = world.spawn((1_i32,));
    let kept = world.new_cref::<i32>(before).unwrap();
    let old = ptr::<i32>(&world, before);

    incr::begin_cycle(&world, &[<i32 as Component>::STABLE_TYPE_ID]);
    assert!(incr::cycle_active(world.gc_world_slot()));
    // A spawn: only the traced column's cell, unarmed.
    let e = world.spawn((3_i32, Tag(1)));
    let (cells, counts) = greyed(&world);
    assert_eq!(cells, vec![ptr::<i32>(&world, e)]);
    assert_eq!(counts.new, 1);
    assert_eq!(flag(cells[0]), 0, "new cells start unarmed");
    // An archetype move: the destination is new (unarmed, greyed), the source a marked
    // tombstone.
    arm(old);
    world.insert_one(before, Tag(2)).unwrap();
    let dst = ptr::<i32>(&world, before);
    assert_eq!(greyed(&world).0, vec![dst]);
    assert_eq!(flag(dst), 0, "the arm stays behind with the tombstone");
    assert!(unsafe { old.chain_kept() }, "the Moved source is marked in this cycle");
    // A despawn's tombstone is marked too, and its pending-dead counterpart.
    let dead = ptr::<Tag>(&world, e);
    world.despawn(e).unwrap();
    assert!(unsafe { dead.chain_kept() });
    incr::end_cycle(world.gc_world_slot());

    // The sweep that ends this cycle keeps the cycle's tombstones, so the forwarding the CRef
    // follows stays whole; the next one may free them.
    unsafe { hecs::gc::sweep(&world) };
    {
        let _scope = GcWorld::new_scope(&mut world);
        assert_eq!(*kept.read(), 1);
    }
    assert!(!unsafe { old.chain_kept() }, "unmarked in the next cycle");
    // Outside the cycle a tombstone is written unmarked again.
    let f = world.spawn((5_i32,));
    let fp = ptr::<i32>(&world, f);
    world.despawn(f).unwrap();
    assert!(!unsafe { fp.chain_kept() });
    cleanup(world);
}

#[test]
fn an_armed_cell_moves_and_despawns_like_a_free_one() {
    let mut world = World::new();
    let e = world.spawn((1_i32,));
    let p = ptr::<i32>(&world, e);
    arm(p);
    // Armed and unborrowed is movable; the move leaves the arm with the tombstone.
    world.insert_one(e, Tag(0)).unwrap();
    assert_eq!(flag(ptr::<i32>(&world, e)), 0);
    // An armed cell despawns (drops) like a free one: Dead, not pending.
    let q = ptr::<Tag>(&world, e);
    arm(q);
    world.despawn(e).unwrap();
    assert_eq!(unsafe { q.header_ptr().as_ref() }.state_name(), "Dead");
    cleanup(world);
}
