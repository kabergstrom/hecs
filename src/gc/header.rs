//! The dense per-cell GC header: one 4-byte word per component cell, stored in a dense array at
//! the start of the cell's column chunk, apart from the values.
//!
//! # Chunk layout
//!
//! Every column chunk is [`DATA_CHUNK_SIZE_BYTES`] (64 KiB), aligned to its size:
//!
//! ```text
//! chunk + 0               ChunkHeader (StorageHeader), 64 bytes
//! chunk + HEADERS_OFFSET  header words: capacity × 4 bytes
//! chunk + values_start    values: capacity × stride bytes
//! ```
//!
//! [`Geometry::of`] gives `capacity`, `values_start` and `stride` from the value's size and
//! alignment alone: `stride` is the size rounded up to the alignment (a zero-sized type takes
//! its alignment, so cells keep distinct addresses), `values_start` is `HEADERS_OFFSET +
//! capacity × 4` rounded up to the alignment, and `capacity` is the largest count that fits.
//!
//! # Address arithmetic
//!
//! A `GCPtr` points at the value. For a value pointer `p` of a `T` column:
//!
//! ```text
//! chunk  = p & !0xFFFF
//! index  = ((p & 0xFFFF) - VALUES_START<T>) / STRIDE<T>     (constant divisor)
//! header = chunk + HEADERS_OFFSET + index * 4
//! ```
//!
//! The typed paths (`CRef<T>`) compute this from `p` and constants of `T` only, so the header
//! load and the value load share no load and overlap on a cold access. The untyped paths
//! (`GCPtr`) read `values_start` and the reciprocal of `stride` from the chunk header instead.
//!
//! # The header word
//!
//! ```text
//! bit 31 ........................ 4 | 3    | 2            | 1 0
//!     borrow flag x (28-bit signed) | mark | pending_dead | state
//! ```
//!
//! - **state** (bits 0–1): [`ALIVE`] = 0, [`DEAD`] = 1, [`MOVED`] = 2, [`FREE`] = 3. Alive is
//!   zero so the fast paths test bits against zero.
//! - **pending_dead** (bit 2): despawned while borrowed; the sweep drops the value once `x` is
//!   0 or 1 (no borrow) and makes the cell `Dead`.
//! - **mark** (bit 3): set to the world's [mark parity](super::mark_parity) when the trace
//!   reaches the cell. The parity flips at the end of every sweep, so a cell is marked in the
//!   current cycle when `mark == parity`; nothing ever clears marks. Every transition out of
//!   Alive (a tombstone: `Dead`, `Moved`, `pending_dead`) writes `!parity`, so a tombstone counts
//!   as marked only once the trace marks it. The sweep recolors every unmarked tombstone (and
//!   unmarked pending cell) it keeps to `parity`, which reads unmarked after the flip; a marked
//!   one reads unmarked after the flip as it is. The trace does not write marks of live cells
//!   (Alive, not pending), which the sweep never frees, and the sweep never writes them: their
//!   mark bit is meaningless.
//! - **borrow flag x** (bits 4–31, two's complement, `x = (word as i32) >> 4`), the incremental
//!   GC's parity encoding:
//!   - `0` free and unarmed, `1` free and armed (the scanner traced the slot in an unfinished
//!     cycle; its first exclusive borrow greys it);
//!   - readers step `x` by `+2`: even values `2, 4, ...` are unarmed readers, odd values
//!     `3, 5, ...` armed readers; a read is `b = x + 2; b > 0`, release `x - 2`;
//!   - writers step `x` by `-2` (a split or clone another `-2`), release `+2`. A writer is never
//!     armed: the low bit means "armed" only for `x >= 0`;
//!   - the scanner arms only non-negative flags (`x |= 1`); disarm is `x &= !1` for `x > 0`;
//!   - overflow is refused: a new reader needs `x < 2^26` ([`READ_REFUSE`] tests bit 30), clones
//!     assert the 28-bit range.
//!
//! New cells are allocated unarmed (`x == 0`), during a cycle too: the engine's new-slot
//! hook greys them. No bit of the word records "allocated this cycle".
//!
//! # Fast paths
//!
//! Each is one load, one masked compare (`test` against an immediate) and one branch:
//!
//! - **read**: `w & READ_REFUSE == 0`, then store `w + STEP`. `READ_REFUSE` covers the state
//!   bits, `pending_dead` and the flag's top two bits, so it passes exactly for Alive, not
//!   pending, `0 <= x < 2^26` (no writer, no overflow). The mark and the arm bit are outside
//!   the mask: armed and plain readers both pass.
//! - **write**: `w & WRITE_REFUSE == 0` (`WRITE_REFUSE = !MARK`), then store
//!   `w - STEP`. It passes exactly for Alive, not pending, `x == 0`: no reader, no writer, not
//!   armed. The cold path takes "Alive, not pending, `x == 1`" (armed and free): grey the slot, then the write,
//!   whose release lands on `x == 0`.
//! - Releases are `w - STEP` (reader) and `w + STEP` (writer): they leave bits 0–3 alone.
//!
//! [`DATA_CHUNK_SIZE_BYTES`]: crate::DATA_CHUNK_SIZE_BYTES

use core::cell::Cell;

/// Bytes per column chunk (64 KiB, the chunk's alignment too).
pub const CHUNK_BYTES: usize = 0x10000;
/// Offset of header word 0 in a chunk: the chunk header ([`ChunkAbi`]) fills the first line.
pub const HEADERS_OFFSET: usize = 64;
/// Bytes per header word.
pub const HEADER_BYTES: usize = 4;

/// State bits.
pub const STATE_MASK: u32 = 0b11;
/// State: holds a value.
pub const ALIVE: u32 = 0;
/// State: no value; references may still name it, so it is not reused.
pub const DEAD: u32 = 1;
/// State: the value moved to another cell, named by the chunk's forwarding table.
pub const MOVED: u32 = 2;
/// State: on the archetype's free list.
pub const FREE: u32 = 3;
/// Despawned while borrowed.
pub const PENDING_DEAD: u32 = 1 << 2;
/// The mark bit (compared with the world's mark parity).
pub const MARK: u32 = 1 << 3;
/// Shift of the borrow flag.
pub const FLAG_SHIFT: u32 = 4;
/// The borrow flag's low bit: armed, for a non-negative flag.
pub const ARMED: u32 = 1 << FLAG_SHIFT;
/// One reader (`+STEP`) or one writer (`-STEP`): the flag's `2`.
pub const STEP: u32 = 2 << FLAG_SHIFT;
/// A new reader is refused when any of these is set: not Alive, pending dead, a writer
/// (`x < 0`) or `x >= 2^26` (overflow guard).
pub const READ_REFUSE: u32 = STATE_MASK | PENDING_DEAD | (1 << 31) | (1 << 30);
/// A new writer is refused (fast path) when any of these is set: everything but the mark.
pub const WRITE_REFUSE: u32 = !MARK;
/// The flag's 28-bit range.
pub const FLAG_MAX: i32 = (1 << 27) - 1;
pub const FLAG_MIN: i32 = -(1 << 27);

/// A fresh Alive word: no borrow, not pending, mark 0, unarmed.
pub const ALIVE_WORD: u32 = ALIVE;
/// A Free word.
pub const FREE_WORD: u32 = FREE;

/// The word's borrow flag `x`.
#[inline(always)]
pub const fn flag(w: u32) -> i32 {
    (w as i32) >> FLAG_SHIFT
}

/// The word's state bits.
#[inline(always)]
pub const fn state(w: u32) -> u32 {
    w & STATE_MASK
}

/// Alive, not pending dead, no borrow of either kind (armed or not): may be moved out,
/// tombstoned or written in place without a guard.
#[inline(always)]
pub const fn is_movable(w: u32) -> bool {
    w & !(MARK | ARMED) == 0
}

/// No borrow of either kind, armed or not (`x` is 0 or 1).
#[inline(always)]
pub const fn is_unborrowed(w: u32) -> bool {
    (w >> FLAG_SHIFT) <= 1
}

/// An exclusive borrow is held.
#[inline(always)]
pub const fn is_writing(w: u32) -> bool {
    flag(w) < 0
}

/// A shared borrow is held.
#[inline(always)]
pub const fn is_reading(w: u32) -> bool {
    flag(w) > 1
}

/// Armed by the incremental scanner (only a non-negative flag can be).
#[inline(always)]
pub const fn is_armed(w: u32) -> bool {
    flag(w) > 0 && w & ARMED != 0
}

/// The read fast path accepts this word.
#[inline(always)]
pub const fn can_read(w: u32) -> bool {
    w & READ_REFUSE == 0
}

/// The write fast path accepts this word.
#[inline(always)]
pub const fn can_write(w: u32) -> bool {
    w & WRITE_REFUSE == 0
}

/// The write cold path accepts this word: Alive, not pending, armed and free (`x == 1`).
#[inline(always)]
pub const fn can_write_armed(w: u32) -> bool {
    w & WRITE_REFUSE == ARMED
}

/// Alive and not pending dead: what `CRef` borrows require.
#[inline(always)]
pub const fn is_live(w: u32) -> bool {
    w & (STATE_MASK | PENDING_DEAD) == ALIVE
}

/// The mark bit for parity `p` (0 or 1).
#[inline(always)]
pub const fn mark_for(p: u32) -> u32 {
    (p & 1) << 3
}

/// Marked in the cycle of parity `p`.
#[inline(always)]
pub const fn is_marked(w: u32, p: u32) -> bool {
    w & MARK == mark_for(p)
}

/// `w` with its state replaced by `s` (a tombstone, Free or Alive) and its mark set to
/// "unmarked in the cycle of parity `p`". Keeps no borrow: tombstoning requires none.
#[inline(always)]
pub const fn tombstone(s: u32, p: u32) -> u32 {
    s | mark_for(p ^ 1)
}

/// What [`HeaderWord::arm`] did.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arm {
    Armed,
    NotAlive,
    WriteBorrowed,
}

/// The bits [`HeaderWord::take_armed`] tests: equal to [`ARMED`] exactly for an Alive cell
/// whose flag is armed (`x > 0`, odd; pending dead included, whose readers may still write
/// nothing).
pub const BARRIER_MASK: u32 = STATE_MASK | ARMED | (1 << 31);

/// Alive and armed: what a disarm clears. `x > 0` with the low bit set is `x >= 1` odd, i.e.
/// the sign bit clear and [`ARMED`] set.
#[inline(always)]
pub const fn needs_disarm(w: u32) -> bool {
    w & BARRIER_MASK == ARMED
}

/// A cell's state, decoded (diagnostics, tests).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SlotState {
    Free,
    Moved,
    Alive,
    Dead,
}

/// One cell's header word. Every access is a `Cell` load or store: borrow guards hold a
/// `&HeaderWord` while the engine may set `pending_dead` or the mark through another.
#[repr(transparent)]
pub struct HeaderWord(pub(crate) Cell<u32>);

impl HeaderWord {
    /// The raw word.
    #[inline(always)]
    pub fn get(&self) -> u32 {
        self.0.get()
    }

    #[inline(always)]
    pub(crate) fn set(&self, w: u32) {
        self.0.set(w)
    }

    /// The decoded state.
    pub fn state(&self) -> SlotState {
        match state(self.get()) {
            ALIVE => SlotState::Alive,
            DEAD => SlotState::Dead,
            MOVED => SlotState::Moved,
            _ => SlotState::Free,
        }
    }

    /// Holds a value: Alive, or despawned while borrowed (`pending_dead`).
    #[inline(always)]
    pub fn is_alive(&self) -> bool {
        state(self.get()) == ALIVE
    }

    /// Alive and not pending dead: the liveness `CRef` checks before borrowing.
    #[inline(always)]
    pub fn is_live(&self) -> bool {
        is_live(self.get())
    }

    /// Despawned while borrowed.
    #[inline(always)]
    pub fn is_pending_dead(&self) -> bool {
        self.get() & PENDING_DEAD != 0
    }

    /// The borrow flag `x`.
    #[inline(always)]
    pub fn borrow_flag(&self) -> i32 {
        flag(self.get())
    }

    /// Marked in the cycle of parity `parity`.
    #[inline(always)]
    pub fn is_marked(&self, parity: u32) -> bool {
        is_marked(self.get(), parity)
    }

    /// Diagnostic name of the state, for resolve-failure logging.
    pub fn state_name(&self) -> &'static str {
        let w = self.get();
        match state(w) {
            ALIVE if w & PENDING_DEAD != 0 => "AlivePendingDead",
            ALIVE => "Alive",
            DEAD => "Dead",
            MOVED => "Moved",
            _ => "Free",
        }
    }

    /// The incremental scan's pre-trace test: `None` unless Alive (pending dead included),
    /// else `Some(!is_writing)`. One load reads both.
    #[inline]
    pub fn readable(&self) -> Option<bool> {
        let w = self.get();
        if state(w) != ALIVE {
            return None;
        }
        Some(!is_writing(w))
    }

    /// The scanner's arm, right after the cell's trace: Alive and `x >= 0` gives `x |= 1`
    /// (readers kept).
    #[inline]
    pub fn arm(&self) -> Arm {
        let w = self.get();
        if state(w) != ALIVE {
            Arm::NotAlive
        } else if (w as i32) < 0 {
            Arm::WriteBorrowed
        } else {
            self.set(w | ARMED);
            Arm::Armed
        }
    }

    /// Disarm: Alive and `x > 0` gives `x &= !1`. Returns whether it was armed.
    #[inline]
    pub fn disarm(&self) -> bool {
        let w = self.get();
        if needs_disarm(w) {
            self.set(w & !ARMED);
            true
        } else {
            false
        }
    }

    /// Armed (and Alive).
    #[inline]
    pub fn is_slot_armed(&self) -> bool {
        needs_disarm(self.get())
    }

    /// The write barrier of an engine raw write (no borrow taken): if Alive and armed, clear
    /// the arm and return `true` (the caller greys the cell). One load and one masked compare
    /// on the unarmed path.
    #[inline(always)]
    pub fn take_armed(&self) -> bool {
        let w = self.get();
        if w & BARRIER_MASK != ARMED {
            return false;
        }
        self.set(w & !ARMED);
        true
    }
}

impl core::fmt::Debug for HeaderWord {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let w = self.get();
        f.debug_struct("HeaderWord")
            .field("state", &self.state_name())
            .field("mark", &((w & MARK) != 0))
            .field("flag", &flag(w))
            .finish()
    }
}

/// Where a column's cells sit in its chunks; a function of the value's size and alignment.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Geometry {
    /// Cells per chunk.
    pub capacity: usize,
    /// Offset of value 0 in a chunk.
    pub values_start: usize,
    /// Bytes per value.
    pub stride: usize,
}

const fn round_up(x: usize, align: usize) -> usize {
    (x + align - 1) & !(align - 1)
}

impl Geometry {
    /// The geometry of a column of values of `size` bytes aligned to `align` (a power of two).
    /// Panics (at compile time in a constant) if not one value fits a chunk.
    pub const fn of(size: usize, align: usize) -> Geometry {
        assert!(align.is_power_of_two());
        let stride = round_up(if size == 0 { 1 } else { size }, align);
        assert!(stride <= CHUNK_BYTES, "component too large for a column chunk");
        let mut capacity = (CHUNK_BYTES - HEADERS_OFFSET) / (HEADER_BYTES + stride);
        loop {
            assert!(capacity > 0, "component too large for a column chunk");
            let values_start = round_up(HEADERS_OFFSET + capacity * HEADER_BYTES, align);
            if values_start <= CHUNK_BYTES && values_start + capacity * stride <= CHUNK_BYTES {
                return Geometry { capacity, values_start, stride };
            }
            capacity -= 1;
        }
    }

    /// The reciprocal the untyped paths divide by `stride` with: `ceil(2^32 / stride)`.
    /// `(offset * recip) >> 32 == offset / stride` for every multiple `offset` of `stride`
    /// below the chunk size.
    pub const fn recip(&self) -> u64 {
        ((1u64 << 32) + self.stride as u64 - 1) / self.stride as u64
    }
}

/// The geometry of `T`'s column, as constants.
pub struct TypedGeometry<T>(core::marker::PhantomData<T>);

impl<T> TypedGeometry<T> {
    pub const GEOMETRY: Geometry = Geometry::of(core::mem::size_of::<T>(), core::mem::align_of::<T>());
    pub const VALUES_START: usize = Self::GEOMETRY.values_start;
    pub const STRIDE: usize = Self::GEOMETRY.stride;
    pub const CAPACITY: usize = Self::GEOMETRY.capacity;
}

/// The header word address of the `T` cell whose value is at `value`: pure arithmetic on the
/// pointer and `T`'s constants (no load).
#[inline(always)]
pub fn typed_header<T>(value: *mut u8) -> *const HeaderWord {
    let p = value as usize;
    let index = (p & (CHUNK_BYTES - 1)).wrapping_sub(TypedGeometry::<T>::VALUES_START)
        / TypedGeometry::<T>::STRIDE;
    // `wrapping_add` keeps provenance from `value`: the header lies in the same chunk.
    value
        .wrapping_sub(p & (CHUNK_BYTES - 1))
        .wrapping_add(HEADERS_OFFSET + index * HEADER_BYTES)
        .cast::<HeaderWord>()
}

/// The layout of the chunk header's fields the untyped paths read, as byte offsets from the
/// chunk start. newgameplus-api reads them too, from its own copy of these constants.
pub struct ChunkAbi;

impl ChunkAbi {
    /// `*mut *mut u8`: the chunk's forwarding table (`capacity` value pointers, indexed like
    /// the header words), null until a cell of the chunk first becomes `Moved`.
    pub const FORWARD: usize = 8;
    /// `u32`: offset of value 0.
    pub const VALUES_START: usize = 32;
    /// `u32`: bytes per value.
    pub const STRIDE: usize = 36;
    /// `u64`: [`Geometry::recip`].
    pub const RECIP: usize = 40;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn word(w: u32) -> HeaderWord {
        HeaderWord(Cell::new(w))
    }

    const fn with_flag(low: u32, x: i32) -> u32 {
        low | ((x << FLAG_SHIFT) as u32)
    }

    #[test]
    fn fresh_alive_reads_and_writes() {
        assert!(can_read(ALIVE_WORD));
        assert!(can_write(ALIVE_WORD));
        assert!(is_movable(ALIVE_WORD));
        assert!(is_live(ALIVE_WORD));
        // The mark never matters to a borrow.
        assert!(can_read(ALIVE_WORD | MARK));
        assert!(can_write(ALIVE_WORD | MARK));
        assert!(is_movable(ALIVE_WORD | MARK));
    }

    #[test]
    fn readers_step_by_two_and_keep_parity() {
        let mut w = ALIVE_WORD;
        for n in 1..=5 {
            assert!(can_read(w));
            w += STEP;
            assert_eq!(flag(w), 2 * n);
            assert!(is_reading(w));
            assert!(!can_write(w) && !can_write_armed(w));
            assert!(!is_movable(w));
        }
        for n in (0..5).rev() {
            w -= STEP;
            assert_eq!(flag(w), 2 * n);
        }
        assert_eq!(w, ALIVE_WORD);
        // Armed readers: odd values above 1, still readable, never writable.
        let mut w = with_flag(0, 1);
        assert!(is_armed(w) && !is_reading(w) && is_unborrowed(w));
        w += STEP;
        assert_eq!(flag(w), 3);
        assert!(is_armed(w) && is_reading(w) && can_read(w));
        assert!(!can_write(w) && !can_write_armed(w));
        w -= STEP;
        assert_eq!(flag(w), 1);
        assert!(can_write_armed(w) && !can_write(w));
    }

    #[test]
    fn writers_step_by_minus_two() {
        let w = ALIVE_WORD | MARK;
        assert!(can_write(w));
        let w1 = w.wrapping_sub(STEP);
        assert_eq!(flag(w1), -2);
        assert_eq!(w1 & (STATE_MASK | PENDING_DEAD | MARK), MARK, "low bits kept");
        assert!(is_writing(w1) && !can_read(w1) && !can_write(w1) && !can_write_armed(w1));
        assert!(!is_armed(w1), "a writer is never armed");
        // A split writer.
        let w2 = w1.wrapping_sub(STEP);
        assert_eq!(flag(w2), -4);
        assert!(!can_read(w2));
        // `b = x + 2; b > 0` refuses every writer count.
        assert!(!can_read(w2.wrapping_add(STEP)));
        let back = w2.wrapping_add(STEP).wrapping_add(STEP);
        assert_eq!(back, w);
    }

    #[test]
    fn armed_free_takes_the_cold_write() {
        let w = with_flag(MARK, 1);
        assert!(!can_write(w));
        assert!(can_write_armed(w));
        assert!(can_read(w));
        assert!(is_movable(w) && is_unborrowed(w));
        // The cold path: grey, then -2 from an unarmed 0; release lands on 0 (unarmed).
        let taken = (w & !ARMED).wrapping_sub(STEP);
        assert_eq!(flag(taken), -2);
        let released = taken.wrapping_add(STEP);
        assert_eq!(flag(released), 0);
        assert!(can_write(released));
    }

    #[test]
    fn arm_and_disarm() {
        let h = word(ALIVE_WORD);
        assert_eq!(h.readable(), Some(true));
        assert_eq!(h.arm(), Arm::Armed);
        assert_eq!(h.borrow_flag(), 1);
        assert!(h.is_slot_armed() && is_armed(h.get()));
        assert!(h.disarm());
        assert_eq!(h.borrow_flag(), 0);
        assert!(!h.disarm(), "already disarmed");
        // Readers: arming makes the count odd, disarm restores it.
        let h = word(with_flag(0, 4));
        assert_eq!(h.arm(), Arm::Armed);
        assert_eq!(h.borrow_flag(), 5);
        assert!(h.disarm());
        assert_eq!(h.borrow_flag(), 4);
        // A writer is never armed.
        let h = word(with_flag(0, -2));
        assert_eq!(h.readable(), Some(false));
        assert_eq!(h.arm(), Arm::WriteBorrowed);
        assert_eq!(h.borrow_flag(), -2);
        assert!(!h.disarm() && !h.is_slot_armed() && !h.take_armed());
        assert_eq!(h.borrow_flag(), -2);
        // Not Alive: neither arms nor reads.
        for s in [DEAD, MOVED, FREE] {
            let h = word(s | MARK);
            assert_eq!(h.readable(), None);
            assert_eq!(h.arm(), Arm::NotAlive);
            assert!(!h.disarm() && !h.take_armed());
            assert_eq!(h.get(), s | MARK);
        }
        // Pending dead is Alive for the scanner.
        let h = word(with_flag(PENDING_DEAD, 2));
        assert_eq!(h.readable(), Some(true));
        assert_eq!(h.arm(), Arm::Armed);
        assert!(h.disarm());
        // Disarming an unarmed 0 does nothing.
        let h = word(ALIVE_WORD | MARK);
        assert!(!h.disarm());
        assert_eq!(h.get(), ALIVE_WORD | MARK);
        // The raw-write barrier: one masked compare; clears the arm, keeps readers and mark.
        let h = word(with_flag(MARK, 1));
        assert!(h.take_armed());
        assert_eq!(h.get(), MARK);
        assert!(!h.take_armed());
        let h = word(with_flag(0, 3));
        assert!(h.take_armed());
        assert_eq!(h.borrow_flag(), 2);
    }

    #[test]
    fn non_alive_and_pending_refuse_everything() {
        for s in [DEAD, MOVED, FREE] {
            for m in [0, MARK] {
                let w = s | m;
                assert!(!can_read(w) && !can_write(w) && !can_write_armed(w));
                assert!(!is_movable(w) && !is_live(w));
            }
        }
        for x in [0, 1, 2, 3, -2] {
            let w = with_flag(PENDING_DEAD, x);
            assert!(!can_read(w) && !can_write(w) && !can_write_armed(w));
            assert!(!is_movable(w) && !is_live(w));
            assert_eq!(is_unborrowed(w), x == 0 || x == 1);
        }
    }

    #[test]
    fn pending_dead_keeps_the_count_through_releases() {
        // A reader and a writer each release onto a pending word.
        let w = with_flag(0, 2) | PENDING_DEAD;
        assert_eq!(flag(w - STEP), 0);
        assert_eq!((w - STEP) & PENDING_DEAD, PENDING_DEAD);
        let w = with_flag(0, -2) | PENDING_DEAD;
        let r = w.wrapping_add(STEP);
        assert_eq!(flag(r), 0);
        assert!(is_unborrowed(r) && r & PENDING_DEAD != 0);
    }

    #[test]
    fn overflow_is_refused() {
        let limit = 1 << 26;
        assert!(can_read(with_flag(0, limit - 2)));
        assert!(can_read(with_flag(0, limit - 1)));
        assert!(!can_read(with_flag(0, limit)));
        assert!(!can_read(with_flag(0, FLAG_MAX)));
        // The largest reader the fast path takes still steps without wrapping.
        assert_eq!(flag(with_flag(0, limit - 1) + STEP), limit + 1);
        assert_eq!(flag(with_flag(0, FLAG_MIN)), FLAG_MIN);
        assert_eq!(flag(with_flag(0, FLAG_MAX)), FLAG_MAX);
    }

    #[test]
    fn marks_flip_with_parity() {
        let w = tombstone(DEAD, 0);
        assert!(!is_marked(w, 0), "a tombstone is unmarked in its cycle");
        assert!(is_marked(w, 1), "and reads marked under the other parity");
        let marked = (w & !MARK) | mark_for(0);
        assert!(is_marked(marked, 0));
        assert_eq!(state(marked), DEAD);
        assert_eq!(state(tombstone(MOVED, 1)), MOVED);
        assert!(!is_marked(tombstone(MOVED, 1), 1));
    }

    #[test]
    fn state_names() {
        assert_eq!(word(ALIVE_WORD).state_name(), "Alive");
        assert_eq!(word(PENDING_DEAD).state_name(), "AlivePendingDead");
        assert_eq!(word(DEAD).state_name(), "Dead");
        assert_eq!(word(MOVED | MARK).state_name(), "Moved");
        assert_eq!(word(FREE).state_name(), "Free");
        assert_eq!(word(FREE).state(), SlotState::Free);
    }

    /// Every geometry fits its chunk, keeps value alignment, and the typed and untyped index
    /// arithmetic agree with the cell index at both ends of the chunk.
    #[test]
    fn geometry_fits_and_indexes() {
        let mut aligns = alloc::vec![];
        let mut a = 1;
        while a <= 32768 {
            aligns.push(a);
            a *= 2;
        }
        for &align in &aligns {
            for size in (0..=600).chain([1000, 4095, 4096, 4097, 20000, 32768, 40000, 65536 - 68]) {
                let size = round_up(size, align);
                if size > CHUNK_BYTES - HEADERS_OFFSET - HEADER_BYTES {
                    continue;
                }
                if round_up(HEADERS_OFFSET + HEADER_BYTES, align) + size.max(align) > CHUNK_BYTES {
                    continue;
                }
                let g = Geometry::of(size, align);
                assert!(g.capacity >= 1, "{size}/{align}");
                assert_eq!(g.values_start % align, 0);
                assert_eq!(g.stride % align, 0);
                assert!(g.stride >= size.max(1));
                assert!(g.values_start >= HEADERS_OFFSET + g.capacity * HEADER_BYTES);
                assert!(g.values_start + g.capacity * g.stride <= CHUNK_BYTES);
                // Maximal: one more would not fit.
                let n = g.capacity + 1;
                assert!(
                    round_up(HEADERS_OFFSET + n * HEADER_BYTES, align) + n * g.stride > CHUNK_BYTES,
                    "{size}/{align} not maximal"
                );
                let recip = g.recip();
                for i in [0, 1, g.capacity / 2, g.capacity - 1].iter().copied().filter(|i| *i < g.capacity) {
                    let off = i * g.stride;
                    assert_eq!(((off as u64 * recip) >> 32) as usize, i, "{size}/{align}");
                    let value_off = g.values_start + off;
                    assert_eq!((value_off - g.values_start) / g.stride, i);
                    assert!(value_off < CHUNK_BYTES);
                }
                // The world's dead slot (value at the chunk's last byte) indexes a word inside
                // its chunk for every geometry.
                let dead_index = (CHUNK_BYTES - 1 - g.values_start) / g.stride;
                assert!(HEADERS_OFFSET + dead_index * HEADER_BYTES + HEADER_BYTES <= CHUNK_BYTES);
            }
        }
    }

    #[test]
    fn awkward_geometries() {
        // A ZST takes its alignment as stride, so cells keep distinct addresses.
        let g = Geometry::of(0, 1);
        assert_eq!(g.stride, 1);
        assert_eq!(g.capacity, (CHUNK_BYTES - HEADERS_OFFSET) / 5);
        let g = Geometry::of(0, 16);
        assert_eq!(g.stride, 16);
        assert_eq!(g.values_start % 16, 0);
        // High alignment.
        let g = Geometry::of(4096, 4096);
        assert_eq!(g.values_start, 4096);
        assert_eq!(g.capacity, 15);
        // Capacity 1.
        let g = Geometry::of(40000, 8);
        assert_eq!(g.capacity, 1);
        assert_eq!(g.values_start, 72); // 68 rounded up to the alignment
        let g = Geometry::of(32768, 32768);
        assert_eq!((g.capacity, g.values_start), (1, 32768));
        // Typed constants match.
        assert_eq!(TypedGeometry::<[u64; 5]>::GEOMETRY, Geometry::of(40, 8));
        assert_eq!(TypedGeometry::<()>::STRIDE, 1);
        assert_eq!(TypedGeometry::<u8>::STRIDE, 1);
    }

    #[test]
    #[should_panic]
    fn too_large_panics() {
        Geometry::of(CHUNK_BYTES - HEADERS_OFFSET, 8);
    }

    #[test]
    fn typed_header_address() {
        // A heap chunk is not 64 KiB aligned; build the address arithmetic on plain numbers.
        fn header_of<T>(chunk: usize, i: usize) -> usize {
            let value = chunk + TypedGeometry::<T>::VALUES_START + i * TypedGeometry::<T>::STRIDE;
            typed_header::<T>(value as *mut u8) as usize
        }
        let chunk = 0x7f12_3456_0000usize;
        for i in [0, 1, 7, TypedGeometry::<[u8; 12]>::CAPACITY - 1] {
            assert_eq!(header_of::<[u8; 12]>(chunk, i), chunk + HEADERS_OFFSET + 4 * i);
        }
        for i in [0, TypedGeometry::<()>::CAPACITY - 1] {
            assert_eq!(header_of::<()>(chunk, i), chunk + HEADERS_OFFSET + 4 * i);
        }
        assert_eq!(header_of::<[u64; 5000]>(chunk, 0), chunk + HEADERS_OFFSET);
    }
}
