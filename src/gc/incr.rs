//! Incremental GC support in the world: per-world cycle state and the grey list.
//!
//! The engine's incremental collector traces a world's cells over several frames. A traced
//! cell is *armed*: the low bit of its borrow flag (bit 4 of the [header word](super::header),
//! set by [`HeaderWord::arm`](super::HeaderWord::arm)). The write fast path (`w &
//! WRITE_REFUSE == 0`) refuses an armed cell, so its first exclusive borrow takes the cold path,
//! [`on_armed_write`](super::on_armed_write), which pushes the cell to this world's grey list
//! before anything can write it; the collector traces it again before the cycle ends. Reads, and
//! writes of unarmed cells, cost nothing extra; nothing costs anything once the cycle ends.
//!
//! While a cycle is active on a world ([`begin_cycle`]):
//! - every cell that becomes `Alive` (spawn, insert, an archetype move's destination, a
//!   migration, a revive) of a traced column type is pushed to the grey list. New cells start
//!   unarmed (`ALIVE_WORD`): they are written right after allocation without a barrier, so the
//!   collector traces them from the grey list;
//! - every tombstone written (`Dead`, `Moved`, `pending_dead`) is written *marked* in the
//!   current cycle's parity ([`GCPtr::parity`](super::GCPtr) answers `parity ^ 1`), so this
//!   cycle's sweep keeps it: a `CRef` the scan met at a live cell (the mark of a live cell is
//!   never written) may name it now, and a `Moved` chain a traced cell follows stays whole.
//!
//! The cycle flag shares the world's mark-parity byte (bit 1 beside the parity's bit 0), so a
//! tombstone write reads both in one load.
//!
//! # What has no write barrier: hecs's native `&mut T`
//!
//! Only a cell's own header word carries the arm bit, so only writes that take its borrow (a
//! gc `CRef` `write`/`try_write`, the engine's API mirror, a raw write followed by
//! [`GCPtr::barrier`](super::GCPtr::barrier)) grey an armed cell. hecs's native `&mut T`
//! fetches borrow a whole column (or nothing) instead and write cells without their words.
//! **They must not write a world while a cycle is active on it**:
//! - checked in debug builds only, by an assert in the column borrow
//!   (`Archetype::borrow_mut`): `World::query`, `World::query_one`, `World::get`,
//!   `EntityRef::get` with a `&mut T` term;
//! - not checked at all (no dynamic borrow): `World::query_mut`, `World::query_one_mut`,
//!   `PreparedQuery::query_mut` / `view_mut`, `World::get_unchecked::<&mut T>`.
//!
//! A release build checks none of them. A reference written through one during a cycle can be
//! missed by the trace and its target freed. The same holds for any raw write through a value
//! pointer that skips [`GCPtr::barrier`](super::GCPtr::barrier).
//!
//! Single-threaded, as every cell access (see [`GCPtr`]'s `Send` impl): the grey list of a
//! world is touched only on the thread that owns the world.

use alloc::vec::Vec;
use core::{cell::RefCell, num::NonZeroU32, sync::atomic::Ordering};

use super::{GCPtr, MARK_PARITY};
use crate::{StableTypeId, World};

/// The cycle bit of a world's [`MARK_PARITY`] byte.
pub(super) const CYCLE: u8 = 2;

/// One world's grey list.
struct Grey {
    /// Cells to trace again: armed cells about to be written, new cells of traced columns.
    cells: Vec<GCPtr>,
    /// The column types the cycle traces, sorted: new cells of other columns are not pushed.
    traced: Vec<StableTypeId>,
    /// Pushes since the last [`take_grey`]: from armed writes, from new cells.
    written: u64,
    new: u64,
}

/// A world's grey list. Not locked: like the header words it records (`Cell`s), it is touched
/// only on the thread that owns the world (the cold write path, the new-cell sites and the
/// collector all run there), and nothing calls out while holding the borrow, so the `RefCell`
/// never conflicts (a conflict would panic, never race).
struct GreySlot(RefCell<Grey>);

// SAFETY: see `GreySlot`: each slot is used only by the thread that owns its world, as the
// header words it records are.
unsafe impl Sync for GreySlot {}

static GREY: [GreySlot; 256] = [const {
    GreySlot(RefCell::new(Grey { cells: Vec::new(), traced: Vec::new(), written: 0, new: 0 }))
}; 256];

/// Start an incremental cycle on `world`, tracing the columns of the `traced` types: from now
/// on armed writes and new cells of those columns go to the grey list, and tombstones are
/// written marked, until [`end_cycle`].
pub fn begin_cycle(world: &World, traced: &[StableTypeId]) {
    let slot = world.world_slot();
    {
        let mut g = GREY[slot.get() as usize].0.borrow_mut();
        g.cells.clear();
        g.traced.clear();
        g.traced.extend_from_slice(traced);
        g.traced.sort_unstable();
        g.written = 0;
        g.new = 0;
    }
    MARK_PARITY[slot.get() as usize].fetch_or(CYCLE, Ordering::Relaxed);
}

/// End the cycle of the world in `world_slot` (finished or abandoned; the world may be gone).
/// The caller disarms what it armed.
pub fn end_cycle(world_slot: NonZeroU32) {
    MARK_PARITY[world_slot.get() as usize].fetch_and(!CYCLE, Ordering::Relaxed);
    let mut g = GREY[world_slot.get() as usize].0.borrow_mut();
    g.cells = Vec::new();
    g.traced = Vec::new();
}

/// Whether a cycle is active on the world in `world_slot`.
#[inline(always)]
pub fn cycle_active(world_slot: NonZeroU32) -> bool {
    MARK_PARITY[world_slot.get() as usize].load(Ordering::Relaxed) & CYCLE != 0
}

/// Pushes to a grey list, by source, since the last [`take_grey`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GreyCounts {
    /// Armed cells written ([`on_armed_write`](super::on_armed_write)).
    pub written: u64,
    /// New cells of traced columns.
    pub new: u64,
}

/// Move the grey list of the world in `world_slot` into `out` (cleared first; the two buffers
/// swap, so neither allocates in steady state), with the push counts since the last take.
pub fn take_grey(world_slot: NonZeroU32, out: &mut Vec<GCPtr>) -> GreyCounts {
    out.clear();
    let mut g = GREY[world_slot.get() as usize].0.borrow_mut();
    core::mem::swap(&mut g.cells, out);
    let counts = GreyCounts { written: g.written, new: g.new };
    g.written = 0;
    g.new = 0;
    counts
}

/// Put `cells` back on the grey list of the world in `world_slot` (the collector's leftovers:
/// a budget spent, or cells still exclusively borrowed).
pub fn push_grey(world_slot: NonZeroU32, cells: &[GCPtr]) {
    GREY[world_slot.get() as usize].0.borrow_mut().cells.extend_from_slice(cells);
}

/// The grey push of an armed write ([`on_armed_write`](super::on_armed_write)'s): only during a
/// cycle (an armed cell outside one is a test's).
#[inline]
pub(super) fn grey_written(slot: GCPtr) {
    let ws = slot.world_slot();
    if cycle_active(ws) {
        let mut g = GREY[ws.get() as usize].0.borrow_mut();
        g.cells.push(slot);
        g.written += 1;
    }
}

/// `slot`, a cell of a `ty()` column, just became `Alive`: during a cycle, grey it if the cycle
/// traces its column. One load of the world's cycle byte otherwise.
#[inline(always)]
pub(crate) fn on_new_cell(slot: GCPtr, ty: impl FnOnce() -> StableTypeId) {
    let ws = slot.world_slot();
    if cycle_active(ws) {
        new_cell_cold(ws, slot, ty());
    }
}

#[cold]
#[inline(never)]
fn new_cell_cold(ws: NonZeroU32, slot: GCPtr, ty: StableTypeId) {
    let mut g = GREY[ws.get() as usize].0.borrow_mut();
    if g.traced.binary_search(&ty).is_ok() {
        g.cells.push(slot);
        g.new += 1;
    }
}

/// [`on_new_cell`] for many cells of one `ty` column of the world in `ws` (a spawn batch, a
/// revive batch): the cycle byte and the type are looked at once.
#[inline]
pub(crate) fn on_new_cells(ws: NonZeroU32, ty: StableTypeId, cells: impl Iterator<Item = GCPtr>) {
    if !cycle_active(ws) {
        return;
    }
    let mut g = GREY[ws.get() as usize].0.borrow_mut();
    if g.traced.binary_search(&ty).is_err() {
        return;
    }
    let before = g.cells.len();
    g.cells.extend(cells);
    g.new += (g.cells.len() - before) as u64;
}
