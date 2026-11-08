//! Dense per-cell header words: the typed address arithmetic for awkward layouts, `Moved`
//! forwarding through the chunk's side table, and the sweep against a reference model.

use hecs::gc::header::{typed_header, TypedGeometry};
use hecs::gc::{GCPtr, SlotState};
use hecs::*;
use std::collections::{HashMap, HashSet};

fn cleanup(mut world: World) {
    world.clear();
    unsafe { hecs::gc::sweep(&world) };
}

fn ptr_of<T: Component>(world: &World, e: Entity) -> GCPtr {
    world.get_gc_ptr_by_id(e, T::STABLE_TYPE_ID).unwrap()
}

fn state(ptr: GCPtr) -> SlotState {
    unsafe { ptr.header_ptr().as_ref().state() }
}

fn cref_ptr<T: Component>(cref: &CRef<T>) -> GCPtr {
    // CRef<T> is a transparent GCPtr.
    unsafe { core::mem::transmute_copy(cref) }
}

macro_rules! component {
    ($t:ty, $name:literal) => {
        impl Component for $t {
            const STABLE_TYPE_ID: StableTypeId = StableTypeId(StableTypeId::fnv1a($name));
        }
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Default)]
struct Zst;
component!(Zst, b"dense::Zst");

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(align(4096))]
struct Page(u64);
component!(Page, b"dense::Page");

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(align(64))]
struct Line(u64, u8);
component!(Line, b"dense::Line");

/// One cell per chunk (40 000 bytes).
#[derive(Debug, Clone, Copy, PartialEq)]
struct Huge([u64; 5000]);
component!(Huge, b"dense::Huge");

#[derive(Debug, Clone, Copy, PartialEq)]
struct Odd([u8; 3]);
component!(Odd, b"dense::Odd");

/// Spawn `n` entities of `make(i)`, then check every cell: the typed header address equals
/// the untyped one, `CRef` reads and writes round-trip, and a despawned cell refuses.
fn exercise<T: Component + Copy + PartialEq + core::fmt::Debug>(
    n: usize,
    make: impl Fn(usize) -> T,
    bump: impl Fn(T) -> T,
) {
    let mut world = World::new();
    let es: Vec<Entity> = (0..n).map(|i| world.spawn((make(i), i as u32))).collect();
    let crefs: Vec<CRef<T>> = es.iter().map(|&e| world.new_cref::<T>(e).unwrap()).collect();
    let mut chunks = HashSet::new();
    for (i, cref) in crefs.iter().enumerate() {
        let ptr = cref_ptr(cref);
        chunks.insert(ptr.value_ptr().as_ptr() as usize & !0xFFFF);
        assert_eq!(
            typed_header::<T>(ptr.value_ptr().as_ptr()) as usize,
            ptr.header_ptr().as_ptr() as usize,
            "cell {i}"
        );
        assert_eq!(ptr.value_ptr().as_ptr() as usize % core::mem::align_of::<T>(), 0);
        assert_eq!(ptr, ptr_of::<T>(&world, es[i]));
    }
    let expected_chunks = n.div_ceil(TypedGeometry::<T>::CAPACITY);
    assert_eq!(chunks.len(), expected_chunks);
    {
        let _scope = GcWorld::new_scope(&mut world);
        for (i, cref) in crefs.iter().enumerate() {
            assert_eq!(*cref.read(), make(i));
            {
                let r1 = cref.try_read().unwrap();
                let r2 = cref.try_read().unwrap();
                assert!(cref.try_write().is_none(), "readers exclude a writer");
                assert_eq!(*r1, *r2);
            }
            {
                let mut w = cref.try_write().unwrap();
                assert!(cref.try_read().is_none(), "a writer excludes readers");
                *w = bump(*w);
            }
            assert_eq!(*cref.try_read().unwrap(), bump(make(i)));
        }
    }
    for (i, &e) in es.iter().enumerate() {
        assert_eq!(*world.get::<&T>(e).unwrap(), bump(make(i)));
        assert_eq!(*world.get::<&u32>(e).unwrap(), i as u32);
    }
    // The query path walks the same values.
    let mut seen = 0;
    for (_, (v, i)) in world.query::<(&T, &u32)>().iter() {
        assert_eq!(*v, bump(make(*i as usize)));
        seen += 1;
    }
    assert_eq!(seen, n);
    world.despawn(es[n / 2]).unwrap();
    {
        let _scope = GcWorld::new_scope(&mut world);
        assert!(crefs[n / 2].try_read().is_none());
        assert!(crefs[n / 2].try_write().is_none());
    }
    assert_eq!(state(cref_ptr(&crefs[n / 2])), SlotState::Dead);
    // The dead slot answers for every layout.
    let dead = world.dead_cref::<T>();
    {
        let _scope = GcWorld::new_scope(&mut world);
        assert!(dead.try_read().is_none());
        assert!(dead.try_write().is_none());
    }
    cleanup(world);
}

#[test]
fn awkward_layouts_through_crefs() {
    // Zero-sized: stride 1, distinct cells.
    exercise(30_000, |_| Zst, |z| z);
    // Byte-sized and odd-sized.
    exercise(40_000, |i| i as u8, |v| v.wrapping_add(1));
    exercise(20_000, |i| Odd([i as u8, (i >> 8) as u8, 7]), |o| Odd([o.0[0], o.0[1], o.0[2] + 1]));
    // High alignment: values start at 4096, 15 per chunk.
    assert_eq!(TypedGeometry::<Page>::VALUES_START, 4096);
    exercise(40, |i| Page(i as u64), |p| Page(p.0 + 1000));
    exercise(3000, |i| Line(i as u64, 1), |l| Line(l.0 * 2, l.1 + 1));
    // Capacity 1: one cell per chunk.
    assert_eq!(TypedGeometry::<Huge>::CAPACITY, 1);
    exercise(5, |i| Huge([i as u64; 5000]), |mut h| {
        h.0[4999] += 1;
        h
    });
}

#[test]
fn moved_cells_forward_through_the_side_table() {
    let mut world = World::new();
    let es: Vec<Entity> = (0..5000).map(|i| world.spawn((i as i32,))).collect();
    let crefs: Vec<CRef<i32>> = es.iter().map(|&e| world.new_cref::<i32>(e).unwrap()).collect();
    let first: Vec<GCPtr> = crefs.iter().map(cref_ptr).collect();
    // Hop 1: (i32,) -> (i32, bool); hop 2: -> (i32, bool, u8); hop 3: back to (i32, bool).
    for &e in &es {
        world.insert_one(e, true).unwrap();
    }
    let second: Vec<GCPtr> = es.iter().map(|&e| ptr_of::<i32>(&world, e)).collect();
    for &e in &es {
        world.insert_one(e, 7u8).unwrap();
    }
    for &e in &es[..2500] {
        world.remove_one::<u8>(e).unwrap();
    }
    for (i, &e) in es.iter().enumerate() {
        assert_eq!(state(first[i]), SlotState::Moved);
        assert_eq!(state(second[i]), SlotState::Moved);
        let now = ptr_of::<i32>(&world, e);
        assert_eq!(first[i].resolve_moved(), now);
        assert_eq!(second[i].resolve_moved(), now);
        assert_eq!(unsafe { world.entity_from_gc_ptr(first[i]) }, Some(e));
    }
    {
        let _scope = GcWorld::new_scope(&mut world);
        for (i, cref) in crefs.iter().enumerate() {
            assert_eq!(*cref.read(), i as i32);
            *cref.write() += 1;
        }
    }
    // Marked chains survive the sweep, hop by hop.
    for cref in &crefs[..100] {
        unsafe { cref_ptr(cref).mark_referenced() };
    }
    let freed = unsafe { hecs::gc::sweep(&world) };
    // Rows: 5000 in (i32,), 5000 in (i32, bool), 2500 in (i32, bool, u8); the first 100
    // chains keep their (i32,) and (i32, bool) rows (and the (i32,bool,u8) rows of those that
    // moved back).
    assert_eq!(freed, 5000 - 100 + 5000 - 100 + 2500 - 100);
    for (i, cref) in crefs[..100].iter().enumerate() {
        assert_eq!(cref_ptr(cref).resolve_moved(), ptr_of::<i32>(&world, es[i]));
        let _scope = GcWorld::new_scope(&mut world);
        assert_eq!(*cref.read(), i as i32 + 1);
    }
    // Unmarked next time: every hop goes, and the chunks' tables with them; new moves
    // allocate fresh tables.
    assert_eq!(unsafe { hecs::gc::sweep(&world) }, 300);
    for &e in &es[..10] {
        world.insert_one(e, 1u16).unwrap();
    }
    let cref = world.new_cref::<i32>(es[0]).unwrap();
    world.insert_one(es[0], 2u64).unwrap();
    {
        let _scope = GcWorld::new_scope(&mut world);
        assert_eq!(*cref.read(), 1);
    }
    cleanup(world);
}

/// A tiny deterministic generator.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

type Row = (usize, u32);

fn row_of(ptr: GCPtr) -> Row {
    (ptr.archetype() as usize, ptr.archetype_slot())
}

/// Random spawns, despawns, moves (insert/remove) and roots across many sweep cycles, against
/// a model of which rows each sweep must free: a tombstone row is freed exactly when no root
/// reaches it (a root reaches every row its entity's `i32` occupied since the root was made).
#[test]
fn sweep_under_random_churn_matches_the_model() {
    for seed in 1..=6u64 {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ seed);
        let mut world = World::new();
        // Entity -> rows its i32 occupied, oldest first (the last is current while alive).
        let mut history: HashMap<Entity, Vec<Row>> = HashMap::new();
        let mut alive: Vec<Entity> = Vec::new();
        // Roots: (cref, entity, index into the entity's history where it starts).
        let mut roots: Vec<(CRef<i32>, Entity, usize)> = Vec::new();
        // Rows that are tombstones and not freed yet.
        let mut tombs: HashSet<Row> = HashSet::new();
        let mut values: HashMap<Entity, i32> = HashMap::new();
        let mut next_value = 0i32;
        for _cycle in 0..40 {
            for _ in 0..rng.below(400) + 50 {
                match rng.below(10) {
                    0..=2 => {
                        next_value += 1;
                        let e = match rng.below(3) {
                            0 => world.spawn((next_value,)),
                            1 => world.spawn((next_value, true)),
                            _ => world.spawn((next_value, 1u8, 2u16)),
                        };
                        let row = row_of(ptr_of::<i32>(&world, e));
                        assert!(!tombs.contains(&row), "reused a row the sweep kept");
                        history.insert(e, vec![row]);
                        values.insert(e, next_value);
                        alive.push(e);
                    }
                    3 if !alive.is_empty() => {
                        let e = alive.swap_remove(rng.below(alive.len()));
                        world.despawn(e).unwrap();
                        tombs.insert(*history[&e].last().unwrap());
                    }
                    4..=5 if !alive.is_empty() => {
                        let e = alive[rng.below(alive.len())];
                        let r = if world.get::<&bool>(e).is_ok() {
                            world.remove_one::<bool>(e).map(|_| ())
                        } else {
                            world.insert_one(e, false)
                        };
                        r.unwrap();
                        let h = history.get_mut(&e).unwrap();
                        tombs.insert(*h.last().unwrap());
                        let row = row_of(ptr_of::<i32>(&world, e));
                        assert!(!tombs.contains(&row), "reused a row the sweep kept");
                        h.push(row);
                    }
                    6..=7 if !alive.is_empty() => {
                        let e = alive[rng.below(alive.len())];
                        let cref = world.new_cref::<i32>(e).unwrap();
                        roots.push((cref, e, history[&e].len() - 1));
                    }
                    8 if !roots.is_empty() => {
                        roots.swap_remove(rng.below(roots.len()));
                    }
                    _ => {}
                }
            }
            // Every root still reads its entity's value, or nothing once despawned.
            {
                let _scope = GcWorld::new_scope(&mut world);
                for (cref, e, _) in &roots {
                    let expect = alive.contains(e).then(|| values[e]);
                    assert_eq!(cref.try_read().map(|v| *v), expect);
                }
            }
            // Model: rows reached by some root.
            let mut reached: HashSet<Row> = HashSet::new();
            for (_, e, from) in &roots {
                reached.extend(history[e][*from..].iter().copied());
            }
            let expect: HashSet<Row> = tombs.difference(&reached).copied().collect();
            // Mark a random half of the roots twice (marking is idempotent), the rest once.
            for (cref, _, _) in &roots {
                let mut p = cref_ptr(cref);
                unsafe { p.mark_referenced() };
                if rng.below(2) == 0 {
                    unsafe { p.mark_referenced() };
                }
            }
            let freed = unsafe { hecs::gc::sweep(&world) };
            assert_eq!(freed as usize, expect.len(), "seed {seed}");
            for row in &expect {
                tombs.remove(row);
            }
            // Histories forget freed rows (no root reaches them, so a root's start lies past
            // the dropped prefix).
            let mut drained: HashMap<Entity, usize> = HashMap::new();
            for (e, h) in history.iter_mut() {
                let keep_from = h
                    .iter()
                    .rposition(|r| expect.contains(r))
                    .map_or(0, |i| i + 1);
                h.drain(..keep_from);
                drained.insert(*e, keep_from);
            }
            for (_, e, from) in &mut roots {
                *from -= drained[e];
            }
            history.retain(|e, h| !h.is_empty() || alive.contains(e));
        }
        drop(roots);
        cleanup(world);
    }
}

/// The incremental collector's word operations on real cells: arm per cell, the dense
/// `disarm_range` pass across chunks, the raw-write barrier and `column_type`.
#[test]
fn arm_disarm_range_and_barrier() {
    use hecs::gc::header::Arm;
    let mut world = World::new();
    let es: Vec<Entity> = (0..20_000).map(|i| world.spawn((i as u64, 1u8))).collect();
    let arch = (0..world.archetype_count())
        .map(|i| world.archetype_at(i).unwrap())
        .find(|a| a.has::<u64>())
        .unwrap();
    let col = arch.column_index(<u64 as Component>::STABLE_TYPE_ID).unwrap();
    let data = unsafe { arch.get_data_storage(col) };
    assert!(data.chunks().len() >= 3);
    let ptrs: Vec<GCPtr> = es.iter().map(|&e| ptr_of::<u64>(&world, e)).collect();
    for (i, p) in ptrs.iter().enumerate() {
        assert_eq!(unsafe { p.column_type() }, <u64 as Component>::STABLE_TYPE_ID);
        if i % 3 == 0 {
            assert_eq!(unsafe { p.header_ptr().as_ref() }.arm(), Arm::Armed);
        }
    }
    // A range across chunk boundaries disarms exactly the armed cells in it.
    let (first, end) = (100u32, 15_000u32);
    let expect = (first..end).filter(|i| i % 3 == 0).count() as u64;
    assert_eq!(unsafe { data.disarm_range(first, end) }, expect);
    for (i, p) in ptrs.iter().enumerate() {
        let w = unsafe { p.header_ptr().as_ref() };
        let in_range = (first as usize..end as usize).contains(&i);
        assert_eq!(w.is_slot_armed(), i % 3 == 0 && !in_range, "cell {i}");
    }
    assert_eq!(unsafe { data.disarm_range(0, 20_000) }, (0..20_000).filter(|i| i % 3 == 0).count() as u64 - expect);
    // The barrier clears an armed cell once (one call of the hook); a write through a CRef
    // sees it unarmed after.
    let hooked = hecs::gc::armed_writes();
    let p = ptrs[7];
    unsafe {
        p.header_ptr().as_ref().arm();
        p.barrier();
        assert!(!p.header_ptr().as_ref().is_slot_armed());
        p.barrier();
    }
    assert_eq!(hecs::gc::armed_writes(), hooked + 1);
    // An armed cell still takes CRef reads and (through the cold path) writes.
    unsafe { ptrs[8].header_ptr().as_ref().arm() };
    let cref = world.new_cref::<u64>(es[8]).unwrap();
    {
        let _scope = GcWorld::new_scope(&mut world);
        assert_eq!(*cref.read(), 8);
        *cref.write() += 1;
    }
    assert!(!unsafe { ptrs[8].header_ptr().as_ref() }.is_slot_armed());
    // The cold write path reached the hook once; the read did not.
    assert_eq!(hecs::gc::armed_writes(), hooked + 2);
    assert_eq!(*world.get::<&u64>(es[8]).unwrap(), 9);
    cleanup(world);
}

/// New cells start unarmed (`x == 0`) whatever the cycle is doing: spawned cells, a move's
/// destination (the arm does not travel with the value; the source becomes a Moved tombstone)
/// and revived cells. The collector greys them through its new-slot hook, not a word bit.
#[test]
fn new_cells_start_unarmed() {
    use hecs::gc::header::{Arm, ALIVE_WORD};
    let mut world = World::new();
    let old: Vec<Entity> = (0..3000).map(|i| world.spawn((i as u64, 0u8))).collect();
    for &e in &old {
        assert_eq!(unsafe { ptr_of::<u64>(&world, e).header_ptr().as_ref() }.arm(), Arm::Armed);
    }
    let fresh: Vec<Entity> = (0..9000).map(|i| world.spawn((i as u64, 1u8))).collect();
    for &e in &fresh {
        assert_eq!(unsafe { ptr_of::<u64>(&world, e).header_ptr().as_ref() }.get(), ALIVE_WORD);
    }
    let src = ptr_of::<u64>(&world, old[5]);
    world.remove_one::<u8>(old[5]).unwrap();
    let moved = ptr_of::<u64>(&world, old[5]);
    assert_eq!(unsafe { moved.header_ptr().as_ref() }.get(), ALIVE_WORD);
    assert_eq!(unsafe { src.header_ptr().as_ref() }.state(), hecs::gc::SlotState::Moved);
    assert_eq!(src.resolve_moved().value(), moved.value());
    // Armed cells stay armed through reads; only the arm's owner (barrier, disarm) clears it.
    let cref = world.new_cref::<u64>(old[6]).unwrap();
    {
        let _scope = GcWorld::new_scope(&mut world);
        assert_eq!(*cref.read(), 6);
    }
    assert!(unsafe { ptr_of::<u64>(&world, old[6]).header_ptr().as_ref() }.is_slot_armed());
    cleanup(world);
}
