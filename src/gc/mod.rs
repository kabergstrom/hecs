mod borrow;
mod gc_world;
pub mod header;
#[allow(missing_documentation)]
pub mod kvec;

pub(crate) mod cells;
pub mod query;
use core::{
    any::{Any, TypeId},
    marker::PhantomData,
    num::NonZeroU32,
    ptr::NonNull,
    sync::atomic::{AtomicU32, AtomicU8, Ordering},
};
pub use gc_world::{GcWorld, GcWorldScope, ReadWorld};
pub use header::{HeaderWord, SlotState};
pub use query::*;

use self::borrow::{BorrowRef, BorrowRefMut, Ref, RefMut};
use self::header::{
    ALIVE, ALIVE_WORD, CHUNK_BYTES, DEAD, FREE, HEADERS_OFFSET, HEADER_BYTES, MARK, MOVED,
    PENDING_DEAD, STATE_MASK,
};
use crate::{
    archetype::{Archetype, StorageHeader},
    Component, Entity, StableTypeId, TypeInfo, World,
};
use alloc::vec::Vec;

/// A pointer to the value of one component cell in a [`World`]'s column storage.
///
/// The cell's [`HeaderWord`] sits in the dense header array of the `CHUNK_BYTES`-aligned chunk
/// the value lives in, and the chunk's storage header at the chunk's start
/// ([`header`](self::header) has the layout and the address arithmetic). The safe methods
/// (`header_ptr`, `world_slot`, `archetype_slot`, `archetype`, `resolve_moved`) read those
/// headers. They are sound because a `GCPtr` is only ever made by hecs from a cell of a live
/// chunk, or through [`GCPtr::from_raw`], whose contract requires the same.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[repr(transparent)]
pub struct GCPtr {
    value: NonNull<u8>,
}
// SAFETY: a `GCPtr` is `Send + Sync` so that `CRef<T>`, and the components holding one, meet
// `Component: Send + Sync`. Nothing reachable through it is synchronized: the cell's header
// word is a `Cell`, and the chunk's forwarding table is written without atomics.
// It is sound only under the engine's invariant that module code, and every touch of a cell
// (deref, `CRef::read`/`write`, `mark_referenced`, `resolve_moved`, `gc::sweep`), runs on the
// thread that owns the `World`. Modules are `no_std` and cannot spawn threads. What would
// break the invariant, and must not be added without first making the headers atomic: running
// module type-op or VFX thunks on worker threads, or parallel physics with module callbacks.
unsafe impl Send for GCPtr {}
// SAFETY: see the `Send` impl above.
unsafe impl Sync for GCPtr {}
impl GCPtr {
    /// Wrap a cell's value pointer.
    ///
    /// # Safety
    /// `value` must be the value pointer of a cell in a still-allocated chunk of a live
    /// [`World`] (any state; the world's [dead slot](World::dead_gc_ptr) counts), and that
    /// `World` must outlive every use of the returned `GCPtr` and of its copies: the safe
    /// methods dereference the cell and chunk headers through it. A placeholder that breaks
    /// this is allowed only if no method is called on it and it is never turned into a `CRef`.
    #[inline]
    pub const unsafe fn from_raw(value: NonNull<u8>) -> Self {
        Self { value }
    }

    /// The cell's value pointer (same as [`value_ptr`](Self::value_ptr)).
    #[inline]
    pub const fn value(&self) -> NonNull<u8> {
        self.value
    }

    #[inline(always)]
    pub(crate) fn storage_header(&self) -> *const StorageHeader {
        let off = self.value.as_ptr() as usize & (CHUNK_BYTES - 1);
        self.value.as_ptr().wrapping_sub(off).cast::<StorageHeader>()
    }

    /// The cell's index in its chunk: the untyped path, through the chunk's storage header
    /// (`values_start` and the stride's reciprocal; no division).
    #[inline(always)]
    fn chunk_index(&self) -> usize {
        let off = self.value.as_ptr() as usize & (CHUNK_BYTES - 1);
        // SAFETY: from_raw's contract: the chunk is allocated and starts with its header.
        let sh = unsafe { &*self.storage_header() };
        let rel = off.wrapping_sub(sh.values_start as usize) as u64;
        (rel.wrapping_mul(sh.recip) >> 32) as usize
    }

    /// The cell's chunk header and index in the chunk, for several accesses to the cell.
    #[inline(always)]
    pub(crate) fn chunk_cell<'a>(&self) -> (&'a StorageHeader, usize) {
        // SAFETY: from_raw's contract: the chunk is allocated and starts with its header.
        (unsafe { &*self.storage_header() }, self.chunk_index())
    }

    /// The cell's header word (untyped: through the chunk's storage header).
    #[inline]
    pub fn header_ptr(&self) -> NonNull<HeaderWord> {
        let index = self.chunk_index();
        let header = self
            .value
            .as_ptr()
            .wrapping_sub(self.value.as_ptr() as usize & (CHUNK_BYTES - 1))
            .wrapping_add(HEADERS_OFFSET + index * HEADER_BYTES);
        // SAFETY: inside the cell's chunk, which is non-null.
        unsafe { NonNull::new_unchecked(header.cast()) }
    }

    /// The header word, for this crate's state transitions.
    ///
    /// # Safety
    /// None beyond `from_raw`'s contract; `unsafe` because the lifetime is unbounded: the
    /// chunk must stay allocated while the reference is used.
    #[inline(always)]
    pub(crate) unsafe fn word<'a>(&self) -> &'a HeaderWord {
        &*self.header_ptr().as_ptr()
    }

    #[inline]
    pub fn world_slot(&self) -> NonZeroU32 {
        unsafe { (&*self.storage_header()).world_slot }
    }
    #[inline]
    pub fn archetype_slot(&self) -> u32 {
        let sh = unsafe { &*self.storage_header() };
        let index = self.chunk_index();
        debug_assert!(index < sh.capacity as usize);
        (sh.chunk_idx as usize * sh.capacity as usize + index) as u32
    }
    #[inline(always)]
    pub fn value_ptr(&self) -> NonNull<u8> {
        self.value
    }

    /// Returns a raw pointer to the owning archetype.
    ///
    /// The back-pointer is written when the chunk is allocated and remains
    /// valid for the lifetime of the archetype, which equals the lifetime of
    /// the owning `World`. Callers must not outlive the `World`.
    #[inline]
    pub fn archetype(&self) -> *const Archetype {
        unsafe { (*self.storage_header()).archetype }
    }

    /// Returns the [`Entity`] associated with this slot. Its id is `u32::MAX` when the row is
    /// free.
    ///
    /// # Safety
    /// - The slot belongs to an archetype: it is not the world's
    ///   [dead slot](World::dead_gc_ptr), whose archetype pointer is null.
    /// - No NS writer on another thread is changing the archetype's entity column (the
    ///   lookup reads it through a shared slice that a concurrent grow could free).
    pub unsafe fn entity(&self) -> Entity {
        (*self.archetype()).entity(self.archetype_slot())
    }

    /// Returns a `GCPtr` to the sibling component of type `id` belonging to
    /// the same entity, or `None` if the archetype does not contain that
    /// component.
    ///
    /// # Safety
    /// - The slot belongs to an archetype (not the world's [dead slot](World::dead_gc_ptr)).
    /// - The slot's row is occupied by an entity (see
    ///   [`Archetype::get_dynamic_by_id`]): a row that was vacated by a move, despawn or sweep
    ///   may since have been reused by another entity, whose sibling this would return.
    /// - No concurrent NS writer on another thread.
    ///
    /// Dereferencing the returned pointer later needs STRUCT, a gc borrow and the matching
    /// type, as for any `GCPtr`.
    pub unsafe fn sibling_by_id(&self, id: StableTypeId) -> Option<GCPtr> {
        (*self.archetype()).get_dynamic_by_id(id, self.archetype_slot())
    }

    /// Returns a `GCPtr` to the sibling component of type `T` belonging to
    /// the same entity, or `None` if the archetype does not contain `T`.
    ///
    /// # Safety
    /// As [`sibling_by_id`](Self::sibling_by_id).
    pub unsafe fn sibling<T: Component>(&self) -> Option<GCPtr> {
        self.sibling_by_id(T::STABLE_TYPE_ID)
    }

    /// Whether the cell is `Alive`, not pending dead, and free of gc borrow guards (armed or
    /// not): the only state in which its value may be moved out (`move_from`, `migrate_from`,
    /// `mark_tombstone`). Insert and remove check every cell they would move with this before
    /// changing anything.
    #[inline]
    pub(crate) fn is_movable(&self) -> bool {
        // SAFETY: the cell is valid by from_raw's contract.
        header::is_movable(unsafe { self.word() }.get())
    }

    /// The world's current mark parity: what a tombstone written now is unmarked under. Every
    /// tombstone write (Dead, Moved, pending_dead) takes its mark from here: the incremental
    /// collector's `on_tombstone` (marked while a cycle is active) is `parity ^ 1` here during
    /// a cycle, in the same single store.
    #[inline]
    fn parity(&self) -> u32 {
        mark_parity(self.world_slot())
    }

    /// Set the cell's state to `Dead` without dropping its value; the caller has taken (or
    /// will take) ownership of the value.
    ///
    /// # Safety
    /// - NS.
    /// - The cell is movable: `Alive`, not pending dead, with no gc borrow guard (`CRef`
    ///   `Ref`/`RefMut`) held on it. Only debug-checked: callers refuse the operation
    ///   beforehand.
    /// - No column borrows on it, and no `&T`/`&mut T` into the value used afterwards.
    /// - The value is moved out exactly once (or deliberately leaked), never dropped in place.
    pub unsafe fn mark_tombstone(&mut self) {
        debug_assert!(self.is_movable(), "tombstoning a borrowed or dead slot");
        self.word().set(header::tombstone(DEAD, self.parity()));
    }

    /// Hand the value to `f` (pointer plus type, for it to move out) and set the cell `Dead`.
    ///
    /// # Safety
    /// As [`mark_tombstone`](Self::mark_tombstone) (the cell is movable: its only caller,
    /// [`TakenEntity`](crate::TakenEntity), comes from [`World::take`](crate::World::take),
    /// which refuses a row with a borrowed cell), and `ty` is the cell's column type. `f` must
    /// move the value out (or leak it); the cell never drops it.
    pub unsafe fn move_value_and_tombstone(
        &mut self,
        ty: &TypeInfo,
        mut f: impl FnMut(*mut u8, TypeInfo),
    ) {
        f(self.value_ptr().as_ptr(), ty.clone());
        self.word().set(header::tombstone(DEAD, self.parity()));
    }

    /// Mark this cell referenced in the current GC cycle (its mark bit takes the world's
    /// [mark parity](mark_parity)), so the tombstone sweep spares it. Propagates along the
    /// `Moved` forwarding chain: a referenced tombstone is only resolvable if every intermediate
    /// hop survives the sweep too.
    ///
    /// A live cell (Alive, not pending dead) is left unwritten: the sweep never frees it, and
    /// its marks are rewritten when it becomes a tombstone. A tombstone already marked in this
    /// cycle stops the walk: its chain was marked with it (the world does not change between
    /// the trace and the sweep).
    ///
    /// # Safety
    /// - NS, and no `gc::sweep` runs concurrently.
    /// - Every cell on the `Moved` chain is in a still-allocated chunk: no sweep has freed a
    ///   hop since this `GCPtr` was last known to reach a referenced cell. (Callers mark from
    ///   roots during a mark phase, before the sweep that would free unmarked hops.)
    pub unsafe fn mark_referenced(&mut self) {
        let (sh, index) = self.chunk_cell();
        // A live cell (the common case) costs its word: the world's parity is read only for a
        // tombstone.
        if !header::is_live(word_at(sh, index).get()) {
            mark_chain(sh, index);
        }
    }

    /// [`mark_referenced`](Self::mark_referenced) with the cell's addressing known (its
    /// type's: a tracer that knows a `CRef`'s target type): a live cell costs the load of its
    /// header word alone, no chunk header read. A tombstone's chain is walked untyped (a hop
    /// may sit in a chunk of another layout).
    ///
    /// # Safety
    /// As [`mark_referenced`](Self::mark_referenced); `at` is the addressing of this cell's
    /// chunk ([`CellAddressing::of`] its column type's geometry): debug builds check it.
    #[inline]
    pub unsafe fn mark_referenced_at(&mut self, at: &header::CellAddressing) {
        debug_assert_eq!(
            at.header(self.value.as_ptr()),
            self.header_ptr().as_ptr().cast_const(),
            "mark_referenced_at: addressing of another geometry than the cell's chunk"
        );
        if !header::is_live((*at.header(self.value.as_ptr())).get()) {
            let (sh, index) = self.chunk_cell();
            mark_chain(sh, index);
        }
    }

    /// Drop the cell's value and set it `Dead`, or, if a gc borrow guard is held on it, set
    /// `pending_dead` so the first `gc::sweep` after the last guard goes drops it.
    ///
    /// # Safety
    /// - NS.
    /// - The cell is `Alive` (else this panics), and `ty` is its column type.
    /// - No column borrows on it, and no `&T`/`&mut T` into the value (other than through a
    ///   gc guard, which the `pending_dead` path keeps valid) is used afterwards.
    pub unsafe fn drop_value_and_tombstone(&mut self, ty: &TypeInfo) {
        let word = self.word();
        let w = word.get();
        if header::state(w) != ALIVE {
            panic!("unexpected state when dropping value: {}", word.state_name());
        }
        let p = self.parity();
        if header::is_unborrowed(w) {
            ty.drop_value(self.value_ptr().as_ptr());
            poison_vacated(self.value_ptr().as_ptr(), ty.value_layout().size());
            word.set(header::tombstone(DEAD, p));
        } else {
            // Keep the flag: the guards release onto it.
            word.set((w & !MARK) | PENDING_DEAD | header::mark_for(p ^ 1));
        }
    }

    /// Move `value` (a `ty`, bitwise) into this free cell and make it `Alive`. The caller must
    /// not use or drop `value` afterwards.
    ///
    /// # Safety
    /// NS; the cell is `Free` (asserted) and of a `ty` column; `value` points to a valid `ty`
    /// that does not overlap the cell.
    pub unsafe fn move_from_value(&mut self, ty: &TypeInfo, value: *mut u8) {
        let word = self.word();
        assert!(header::state(word.get()) == FREE);
        word.set(ALIVE_WORD);
        core::ptr::copy_nonoverlapping(value, self.value_ptr().as_ptr(), ty.value_layout().size());
    }

    /// Move `src`'s value (a `ty`, bitwise) into this free cell; `src` becomes a `Moved`
    /// tombstone forwarding here.
    ///
    /// # Safety
    /// NS; this cell is `Free` and of a `ty` column; `src` is a different, movable cell
    /// ([`is_movable`](Self::is_movable)) of a `ty` column, checked by the caller before the
    /// operation began (only debug-asserted here); no column borrows on `src`.
    pub(crate) unsafe fn move_from(&mut self, ty: &TypeInfo, src: GCPtr) {
        debug_assert!(src != *self);
        debug_assert!(header::state(self.word().get()) == FREE);
        // Need source to be alive with no active borrows: callers check before they start.
        debug_assert!(src.is_movable(), "moving a borrowed or dead slot");
        self.word().set(ALIVE_WORD);
        src.set_moved(*self);
        core::ptr::copy_nonoverlapping(
            src.value_ptr().as_ptr(),
            self.value_ptr().as_ptr(),
            ty.value_layout().size(),
        );
        poison_vacated(src.value_ptr().as_ptr(), ty.value_layout().size());
    }

    /// Like `move_from`, but `f(src_value, dst_value)` builds the destination
    /// value (a layout change) instead of a bitwise copy. `f` consumes the
    /// source value; it is never dropped.
    ///
    /// # Safety
    /// As [`move_from`](Self::move_from), with `f` initializing a valid value of this cell's
    /// column type from `src`'s.
    pub(crate) unsafe fn migrate_from(&mut self, src: GCPtr, f: impl FnOnce(*mut u8, *mut u8)) {
        debug_assert!(src != *self);
        debug_assert!(header::state(self.word().get()) == FREE);
        debug_assert!(src.is_movable(), "migrating a borrowed or dead slot");
        self.word().set(ALIVE_WORD);
        src.set_moved(*self);
        f(src.value_ptr().as_ptr(), self.value_ptr().as_ptr());
    }

    /// Make this movable cell (or a vacant `Dead` one: a revive pointing a row its entity left
    /// at it) a `Moved` tombstone forwarding to `target`: the state goes in the header word,
    /// the target in the chunk's forwarding table (allocated with the chunk's first `Moved`
    /// cell; the sweep frees it once the chunk has none). Written unmarked, like every
    /// tombstone.
    ///
    /// # Safety
    /// NS; the cell is movable, or `Dead` (not `Moved`: its table entry would leak a count).
    #[inline]
    pub(crate) unsafe fn set_moved(&self, target: GCPtr) {
        let (sh, index) = self.chunk_cell();
        set_moved_at(sh, index, target);
    }

    /// The cell this `Moved` cell forwards to.
    ///
    /// # Safety
    /// The cell is `Moved`.
    #[inline]
    pub(crate) unsafe fn forward_target(&self) -> GCPtr {
        let (sh, index) = self.chunk_cell();
        forward_at(sh, index)
    }

    /// Leave the `Moved` state's bookkeeping: forget the forwarding entry. The table stays
    /// (the sweep frees it once the chunk has no `Moved` cell: no free and reallocation per
    /// revive or move). The caller rewrites the header word.
    ///
    /// # Safety
    /// NS; the cell is `Moved`.
    #[inline]
    pub(crate) unsafe fn clear_moved(&self) {
        let (sh, index) = self.chunk_cell();
        clear_moved_at(sh, index);
    }

    /// Follow the `Moved` chain to the current location.
    #[inline]
    pub fn resolve_moved(&self) -> Self {
        let mut ptr = *self;
        // SAFETY: from_raw's contract keeps every hop's chunk allocated. One index per hop:
        // the word and the table entry share it.
        unsafe {
            loop {
                let (sh, index) = ptr.chunk_cell();
                if header::state(word_at(sh, index).get()) != MOVED {
                    return ptr;
                }
                ptr = forward_at(sh, index);
            }
        }
    }

    /// The `StableTypeId` of this cell's column, through the chunk's storage header (its
    /// archetype and column index; no search).
    ///
    /// # Safety
    /// The cell is in an archetype chunk (not the world's dead slot) and its archetype is
    /// alive.
    #[inline]
    pub unsafe fn column_type(&self) -> StableTypeId {
        let sh = &*self.storage_header();
        (*sh.archetype).types()[sh.column as usize].id()
    }

    /// The write barrier of an engine raw write (no borrow taken): if the cell is Alive and
    /// armed, clear the arm and grey it (the [`on_armed_write`] hook). One load and one masked
    /// compare when unarmed; untyped addressing (the chunk header's geometry).
    ///
    /// # Safety
    /// NS.
    #[inline(always)]
    pub unsafe fn barrier(&self) {
        if self.word().take_armed() {
            on_armed_write(*self);
        }
    }

    /// For verification after a trace: every hop of the `Moved` chain from here is marked in
    /// the current cycle, ending at an Alive cell, or at a Dead one that is marked. (A Free
    /// end is never kept: a freed cell's word carries no mark.)
    ///
    /// # Safety
    /// As [`mark_referenced`](Self::mark_referenced).
    pub unsafe fn chain_kept(&self) -> bool {
        let p = self.parity();
        let mut ptr = *self;
        loop {
            let w = ptr.word().get();
            match header::state(w) {
                ALIVE => return true,
                DEAD => return header::is_marked(w, p),
                MOVED if header::is_marked(w, p) => ptr = ptr.forward_target(),
                _ => return false,
            }
        }
    }
}

#[derive(Clone)]
pub struct CRef<T: Component> {
    pub(crate) ptr: GCPtr,
    pub(crate) _marker: PhantomData<&'static T>,
}

#[cfg(feature = "mirror_mirror")]
impl<T: Clone + Component> Reflect for CRef<T> {
    fn type_descriptor(&self) -> alloc::borrow::Cow<'static, mirror_mirror::TypeDescriptor> {
        todo!()
    }

    fn as_any(&self) -> &dyn Any {
        todo!()
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        todo!()
    }

    fn as_reflect(&self) -> &dyn Reflect {
        todo!()
    }

    fn as_reflect_mut(&mut self) -> &mut dyn Reflect {
        todo!()
    }

    fn reflect_owned(self: Box<Self>) -> mirror_mirror::ReflectOwned {
        todo!()
    }

    fn reflect_ref(&self) -> mirror_mirror::ReflectRef<'_> {
        todo!()
    }

    fn reflect_mut(&mut self) -> ReflectMut<'_> {
        todo!()
    }

    fn patch(&mut self, value: &dyn Reflect) {
        todo!()
    }

    fn to_value(&self) -> mirror_mirror::Value {
        todo!()
    }

    fn clone_reflect(&self) -> Box<dyn Reflect> {
        todo!()
    }

    fn debug(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl<T: core::fmt::Debug + Component> core::fmt::Debug for CRef<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("CRef")
            .field("type", &core::any::type_name::<T>())
            .field("ptr", &self.ptr.resolve_moved())
            .finish()
    }
}

impl<T: Component> CRef<T> {
    /// The cell's header word by `T`'s address arithmetic: no load (see [`header`]).
    #[inline(always)]
    fn typed_word(&self) -> &HeaderWord {
        // SAFETY: a `CRef<T>` names a cell of a `T` column (its constructors' contract), in a
        // chunk the world keeps allocated (`GCPtr::from_raw`'s), laid out by `T`'s geometry.
        unsafe { &*header::typed_header::<T>(self.ptr.value.as_ptr()) }
    }

    fn live_ptr(&self) -> Option<GCPtr> {
        let ptr = self.ptr.resolve_moved();
        if !header::is_live(unsafe { ptr.word() }.get()) {
            return None;
        }
        Some(ptr)
    }

    pub fn ptr_eq(&self, other: &Self) -> bool {
        let a = self.ptr.resolve_moved();
        let b = other.ptr.resolve_moved();
        a == b
    }

    /// Returns the [`Entity`] this component belongs to.
    pub fn entity(&self) -> Entity {
        let ptr = self
            .live_ptr()
            .expect("CRef::entity called on a deleted component");
        unsafe { ptr.entity() }
    }

    /// Returns a `CRef<U>` to a sibling component on the same entity, or
    /// `None` if the archetype does not contain `U`.
    pub fn sibling<U: Component>(&self) -> Option<CRef<U>> {
        let ptr = self.live_ptr()?;
        let sibling_ptr = unsafe { ptr.sibling::<U>()? };
        Some(CRef {
            ptr: sibling_ptr,
            _marker: PhantomData::default(),
        })
    }

    #[inline(always)]
    pub fn read(&self) -> Ref<'_, T> {
        match slot_mode(self.ptr.world_slot()) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::GcDynamic | SlotMode::ReadOnly => {}
        }
        match BorrowRef::new(self.typed_word()) {
            Some(borrow) => Ref {
                value: self.ptr.value_ptr().cast(),
                borrow,
            },
            None => self.read_cold(),
        }
    }

    /// Not readable in place: `Moved` (follow it), not live, or borrowed.
    #[cold]
    #[inline(never)]
    fn read_cold(&self) -> Ref<'_, T> {
        let ptr = self.ptr.resolve_moved();
        let word = unsafe { ptr.word() };
        if !word.is_live() {
            panic!("Borrowing a deleted component")
        }
        let borrow = BorrowRef::new(word).expect("already mutably borrowed");
        Ref {
            value: ptr.value_ptr().cast(),
            borrow,
        }
    }

    #[inline(always)]
    pub fn try_read(&self) -> Option<Ref<'_, T>> {
        match slot_mode(self.ptr.world_slot()) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::GcDynamic | SlotMode::ReadOnly => {}
        }
        match BorrowRef::new(self.typed_word()) {
            Some(borrow) => Some(Ref {
                value: self.ptr.value_ptr().cast(),
                borrow,
            }),
            None => self.try_read_cold(),
        }
    }

    #[cold]
    #[inline(never)]
    fn try_read_cold(&self) -> Option<Ref<'_, T>> {
        let ptr = self.ptr.resolve_moved();
        let word = unsafe { ptr.word() };
        if !word.is_live() {
            return None;
        }
        Some(Ref {
            value: ptr.value_ptr().cast(),
            borrow: BorrowRef::new(word)?,
        })
    }

    #[inline(always)]
    pub fn write(&self) -> RefMut<'_, T> {
        match slot_mode(self.ptr.world_slot()) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::ReadOnly => panic!("CRef::write during ReadWorld scope"),
            SlotMode::GcDynamic => {}
        }
        match BorrowRefMut::new(self.typed_word(), self.ptr) {
            Some(borrow) => RefMut {
                value: self.ptr.value_ptr().cast(),
                borrow,
                marker: Default::default(),
            },
            None => self.write_cold(),
        }
    }

    #[cold]
    #[inline(never)]
    fn write_cold(&self) -> RefMut<'_, T> {
        let ptr = self.ptr.resolve_moved();
        let word = unsafe { ptr.word() };
        if !word.is_live() {
            panic!("Borrowing a deleted component")
        }
        let borrow = BorrowRefMut::new(word, ptr).expect("already borrowed");
        RefMut {
            value: ptr.value_ptr().cast(),
            borrow,
            marker: Default::default(),
        }
    }

    #[inline(always)]
    pub fn try_write(&self) -> Option<RefMut<'_, T>> {
        match slot_mode(self.ptr.world_slot()) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::ReadOnly => panic!("CRef::try_write during ReadWorld scope"),
            SlotMode::GcDynamic => {}
        }
        match BorrowRefMut::new(self.typed_word(), self.ptr) {
            Some(borrow) => Some(RefMut {
                value: self.ptr.value_ptr().cast(),
                borrow,
                marker: Default::default(),
            }),
            None => self.try_write_cold(),
        }
    }

    #[cold]
    #[inline(never)]
    fn try_write_cold(&self) -> Option<RefMut<'_, T>> {
        let ptr = self.ptr.resolve_moved();
        let word = unsafe { ptr.word() };
        if !word.is_live() {
            return None;
        }
        Some(RefMut {
            value: ptr.value_ptr().cast(),
            borrow: BorrowRefMut::new(word, ptr)?,
            marker: Default::default(),
        })
    }

    /// Cheap, lifetime-bound deref valid only while a [`ReadWorld`] scope is active.
    ///
    /// # Why this is faster than [`read`](Self::read)
    ///
    /// The dynamic path ([`read`](Self::read)) does, on every call:
    /// - an atomic load of the per-slot mode flag,
    /// - a load + branch + **store** on the cell's header word (reader increment),
    /// - constructs a `Ref<'_, T>` whose `Drop` does another load + store (decrement).
    ///
    /// `read_bypass` does, on every call:
    /// - a load + masked test + branch on the header word (to reject a held `RefMut`, a dead
    ///   or a moved cell),
    /// - a pointer cast to `&T`.
    ///
    /// In raw cycles the saved work is small (~7–12 cycles per access). The bigger
    /// wins are second-order: no writes to the header word means its cache line stays
    /// clean across reads, and returning a bare `&T` (instead of a `Ref` with a
    /// non-trivial `Drop`) lets the compiler hoist loads out of loops, vectorize, and
    /// treat the borrow as `noalias` — none of which it can do through `Ref<'_, T>`.
    ///
    /// # Soundness
    ///
    /// Three things keep this sound and they all matter:
    /// 1. `&'s ReadWorld<'_>` ties `&'s T`'s lifetime to the scope, and the scope
    ///    blocks `GcWorld` mutation (`spawn`/`despawn`/`insert`/...) and `CRef::write`
    ///    while alive.
    /// 2. The world-identity `assert_eq!` rejects a `ReadWorld` from a different
    ///    `World` (whose mutation would not be blocked).
    /// 3. The "no writer" check rejects calls made while a `RefMut` is held
    ///    (which could pre-date the scope, since the scope can't retroactively cancel
    ///    an outstanding mutable borrow). Without this check, `&mut T` and `&T` could
    ///    coexist in safe code.
    #[inline(always)]
    pub fn read_bypass<'s>(&self, scope: &'s ReadWorld<'_>) -> &'s T {
        assert_eq!(
            self.ptr.world_slot(),
            scope.world_slot(),
            "CRef belongs to a different World than the ReadWorld scope"
        );
        // Alive, not pending dead, no writer (`x >= 0`).
        const REFUSE: u32 = STATE_MASK | PENDING_DEAD | (1 << 31);
        if self.typed_word().get() & REFUSE == 0 {
            return unsafe { self.ptr.value_ptr().cast::<T>().as_ref() };
        }
        self.read_bypass_cold()
    }

    #[cold]
    #[inline(never)]
    fn read_bypass_cold<'s>(&self) -> &'s T {
        let ptr = self.ptr.resolve_moved();
        let word = unsafe { ptr.word() };
        if !word.is_live() {
            panic!("Borrowing a deleted component")
        }
        assert!(
            !header::is_writing(word.get()),
            "CRef::read_bypass while a mutable borrow is held"
        );
        unsafe { ptr.value_ptr().cast::<T>().as_ref() }
    }

    /// Read the component with no runtime checks at all. The caller takes
    /// responsibility for every invariant that [`read_bypass`](Self::read_bypass)
    /// would otherwise verify.
    ///
    /// This is the fastest possible read path: a single pointer cast plus
    /// dereference. No header load, no atomic load, no branches. In a tight
    /// loop the compiler can hoist this trivially and the value's cache line
    /// stays clean.
    ///
    /// # Safety
    ///
    /// All of the following must hold for the duration of `'s`:
    /// 1. `scope` is a [`ReadWorld`] of the same [`World`] this `CRef` was
    ///    obtained from.
    /// 2. The `CRef` points to the component's current location. In particular,
    ///    no archetype change (`insert`/`remove`) has moved this component
    ///    since the `CRef` was captured. This is automatic if the `CRef` was
    ///    obtained from a query *inside* this `ReadWorld` scope, since the
    ///    scope blocks archetype changes.
    /// 3. The component has not been despawned and is still Alive and not
    ///    pending dead.
    /// 4. No `RefMut<'_, T>` for this component is held anywhere, including
    ///    `RefMut`s acquired before the `ReadWorld` scope began and not yet
    ///    dropped.
    ///
    /// Violating any of these is undefined behavior. Prefer
    /// [`read_bypass`](Self::read_bypass) unless profiling shows the asserts
    /// dominate.
    #[inline]
    pub unsafe fn read_bypass_unchecked<'s>(&self, _scope: &'s ReadWorld<'_>) -> &'s T {
        unsafe { self.ptr.value_ptr().cast::<T>().as_ref() }
    }
}

/// The incremental collector's write barrier: the first exclusive borrow of an armed cell
/// (one its scanner traced in an unfinished cycle), or a raw write through
/// [`GCPtr::barrier`], lands here after clearing the arm and before it may write. Every
/// armed-write path reaches this one function: hecs's own borrow cold path and barrier, and
/// the module API's cold path (the engine routes `newgameplus_api`'s `armed_write` here through
/// its CRef bridge).
///
/// No collector arms cells yet (only [`HeaderWord::arm`] does, which nothing but tests calls),
/// and a cell nobody armed needs no grey, so this greys nothing: the incremental collector
/// greys `slot` here. It counts the calls per thread ([`armed_writes`]); the count costs a
/// thread-local increment on this cold path only.
#[cold]
#[inline(never)]
pub fn on_armed_write(slot: GCPtr) {
    #[cfg(feature = "std")]
    ARMED_WRITES.with(|c| c.set(c.get() + 1));
    let _ = slot;
}

#[cfg(feature = "std")]
std::thread_local! {
    static ARMED_WRITES: core::cell::Cell<u64> = const { core::cell::Cell::new(0) };
}

/// How many armed writes ([`on_armed_write`]) this thread has made (0 without `std`). Tests
/// check with it that every armed-write path reaches the hook; a collector can count greys from
/// writes with it.
pub fn armed_writes() -> u64 {
    #[cfg(feature = "std")]
    return ARMED_WRITES.with(|c| c.get());
    #[cfg(not(feature = "std"))]
    0
}

/// Header word `index` of the chunk headed by `sh`.
///
/// # Safety
/// `index` is below the chunk's capacity; the chunk stays allocated while the reference is
/// used.
#[inline(always)]
pub(crate) unsafe fn word_at<'a>(sh: &StorageHeader, index: usize) -> &'a HeaderWord {
    &*(sh as *const StorageHeader)
        .cast::<u8>()
        .add(HEADERS_OFFSET + index * HEADER_BYTES)
        .cast::<HeaderWord>()
}

/// The cell `index` of the chunk headed by `sh`.
///
/// # Safety
/// `index` is below the chunk's capacity; as [`GCPtr::from_raw`].
#[inline(always)]
pub(crate) unsafe fn value_at(sh: &StorageHeader, index: usize) -> GCPtr {
    GCPtr::from_raw(NonNull::new_unchecked(
        (sh as *const StorageHeader as *mut u8).add(sh.values_start as usize + index * sh.stride as usize),
    ))
}

/// Where `Moved` cell `index` of the chunk headed by `sh` forwards to.
///
/// # Safety
/// Cell `index` of the chunk is `Moved`.
#[inline(always)]
pub(crate) unsafe fn forward_at(sh: &StorageHeader, index: usize) -> GCPtr {
    let table = sh.forward.get();
    debug_assert!(!table.is_null(), "Moved cell without a forwarding table");
    let target = *table.add(index);
    debug_assert!(!target.is_null(), "Moved cell without a forwarding entry");
    GCPtr::from_raw(NonNull::new_unchecked(target))
}

/// [`GCPtr::mark_referenced`] from cell `index` of the chunk headed by `sh`, a cell that is
/// not live: mark it and every hop of its `Moved` chain, up to a live cell or a tombstone
/// already marked in this cycle.
///
/// # Safety
/// As [`GCPtr::mark_referenced`].
unsafe fn mark_chain(mut sh: &StorageHeader, mut index: usize) {
    let p = mark_parity(sh.world_slot);
    loop {
        let word = word_at(sh, index);
        let w = word.get();
        if header::is_live(w) || (header::state(w) != ALIVE && header::is_marked(w, p)) {
            return;
        }
        word.set((w & !MARK) | header::mark_for(p));
        if header::state(w) != MOVED {
            return;
        }
        (sh, index) = forward_at(sh, index).chunk_cell();
    }
}

/// [`GCPtr::set_moved`] of cell `index` of the chunk headed by `sh`.
///
/// # Safety
/// As [`GCPtr::set_moved`].
#[inline(always)]
pub(crate) unsafe fn set_moved_at(sh: &StorageHeader, index: usize, target: GCPtr) {
    let table = sh.forward_table_or_alloc();
    *table.add(index) = target.value.as_ptr();
    sh.moved.set(sh.moved.get() + 1);
    word_at(sh, index).set(header::tombstone(MOVED, mark_parity(sh.world_slot)));
}

/// [`GCPtr::clear_moved`] of cell `index` of the chunk headed by `sh`.
///
/// # Safety
/// NS; cell `index` of the chunk is `Moved`.
#[inline(always)]
pub(crate) unsafe fn clear_moved_at(sh: &StorageHeader, index: usize) {
    debug_assert!(!sh.forward.get().is_null());
    // Debug builds forget the entry, so a stale read asserts; release leaves the table line
    // clean (an entry is read only while its cell is `Moved`).
    #[cfg(debug_assertions)]
    {
        *sh.forward.get().add(index) = core::ptr::null_mut();
    }
    let _ = index;
    sh.moved.set(sh.moved.get() - 1);
}

/// Sweep tombstones from the world, freeing rows where all cells are `Dead`/`Moved` and not
/// marked in this cycle, counting each free in the row's
/// [`row_generation`](crate::Archetype::row_generation); first drops the values of
/// `pending_dead` cells whose borrows are gone; frees the forwarding tables of chunks left
/// with no `Moved` cell. Then flips the world's
/// [mark parity](mark_parity): marks set in this cycle read as unmarked in the next, so nothing
/// resets them.
///
/// The sweep reads the dense header arrays word by word (a block test that the compiler
/// vectorizes) and touches the headers and values of candidate cells only: live cells are
/// read, never written.
///
/// Nothing else keeps a tombstone: copies of cell memory that may point at one (rollback
/// history) must be traced as roots, so that it is marked.
///
/// Call this after marking live cells with `GCPtr::mark_referenced()`.
/// Returns the number of entity slots freed.
///
/// # Safety
/// Must not be called while any `GcWorld` or `ReadWorld` scope is active, or while
/// component borrows are held.
pub unsafe fn sweep(world: &World) -> u32 {
    assert_eq!(
        slot_mode(world.world_slot()),
        SlotMode::Off,
        "sweep called while a GcWorld or ReadWorld scope is active"
    );
    let p = mark_parity(world.world_slot());
    let marked = header::mark_for(p);
    let mut freed = 0u32;
    // Column 0's unmarked tombstones (sorted), and whether every other column of the row is an
    // unmarked tombstone too.
    let mut candidates: Vec<u32> = Vec::new();
    let mut freeable: Vec<bool> = Vec::new();
    for (_, archetype) in world.archetypes() {
        let count = archetype.allocated_values_nonsync();
        let types = archetype.types();
        if count == 0 || types.is_empty() {
            continue;
        }
        candidates.clear();
        freeable.clear();
        for (col, ty) in types.iter().enumerate() {
            let data = archetype.get_data_storage(col);
            let first = col == 0;
            let mut cursor = 0usize;
            data.scan_headers(
                count,
                |w| {
                    // Pending dead, or a tombstone unmarked in this cycle: `(w ^ marked) &
                    // (STATE | MARK)` is `MARK|DEAD` or `MARK|MOVED`.
                    let t = (w ^ marked) & (STATE_MASK | MARK);
                    (w & PENDING_DEAD != 0) | (t.wrapping_sub(MARK | DEAD) < 2)
                },
                |slot, word| {
                    let mut w = word.get();
                    if w & PENDING_DEAD != 0 && header::is_unborrowed(w) {
                        ty.drop_value(data.value_ptr(slot).as_ptr());
                        poison_vacated(data.value_ptr(slot).as_ptr(), ty.value_layout().size());
                        w = DEAD | (w & MARK);
                        word.set(w);
                    }
                    if header::is_marked(w, p) {
                        return;
                    }
                    let s = header::state(w);
                    let tomb = s == DEAD || s == MOVED;
                    if first {
                        if tomb {
                            candidates.push(slot);
                            freeable.push(true);
                        }
                    } else {
                        while cursor < candidates.len() && candidates[cursor] < slot {
                            freeable[cursor] = false;
                            cursor += 1;
                        }
                        if cursor < candidates.len() && candidates[cursor] == slot {
                            freeable[cursor] &= tomb;
                            cursor += 1;
                        }
                    }
                    // Unmarked and surviving this sweep (unless its row is freed below): recolor
                    // it so it reads unmarked after the parity flip too.
                    word.set(w ^ MARK);
                },
            );
            if !first {
                for ok in &mut freeable[cursor..] {
                    *ok = false;
                }
            }
        }
        for (&slot, &ok) in candidates.iter().zip(&freeable) {
            if ok {
                archetype.free_slot(slot);
                freed += 1;
            }
        }
        // Forwarding tables outlive their chunk's last `Moved` cell until here.
        for col in 0..types.len() {
            for &chunk in archetype.get_data_storage(col).chunks() {
                let sh = &*chunk.cast::<StorageHeader>();
                if sh.moved.get() == 0 {
                    sh.free_forward_table();
                }
            }
        }
    }
    flip_mark_parity(world.world_slot());
    freed
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum SlotMode {
    Off = 0,
    GcDynamic = 1,
    ReadOnly = 2,
}

static SLOT_MODE: [AtomicU8; 256] = [const { AtomicU8::new(0) }; 256];
// AtomicU32 so the counter can never realistically wrap (would require 2^32 live ReadWorld
// scopes on the same slot); the assert in `enter_read_only` is belt-and-suspenders.
static READ_ONLY_DEPTH: [AtomicU32; 256] = [const { AtomicU32::new(0) }; 256];
static WORLD_SLOT_ALLOCATED: [AtomicU8; 256] = [const { AtomicU8::new(0) }; 256];

#[inline]
pub(crate) fn slot_mode(slot: NonZeroU32) -> SlotMode {
    match SLOT_MODE[slot.get() as usize].load(Ordering::Relaxed) {
        0 => SlotMode::Off,
        1 => SlotMode::GcDynamic,
        2 => SlotMode::ReadOnly,
        _ => unreachable!(),
    }
}

pub(crate) fn alloc_world_slot() -> NonZeroU32 {
    for i in 1..WORLD_SLOT_ALLOCATED.len() {
        if WORLD_SLOT_ALLOCATED[i]
            .compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            return NonZeroU32::new(i as u32).unwrap();
        }
    }
    panic!("max 256 worlds active concurrently")
}

/// Release a world slot for reuse.
///
/// # Safety
/// `slot` was allocated by `alloc_world_slot` for a `World` being dropped: no `GCPtr`, `CRef`
/// or guard of that world is used afterwards (a reused slot would make them look like
/// another world's).
pub(crate) unsafe fn free_world_slot(slot: NonZeroU32) {
    // Defensive: ensure a freed slot can't leak GcDynamic/ReadOnly into its next user.
    SLOT_MODE[slot.get() as usize].store(SlotMode::Off as u8, Ordering::Relaxed);
    READ_ONLY_DEPTH[slot.get() as usize].store(0, Ordering::Relaxed);
    MARK_PARITY[slot.get() as usize].store(0, Ordering::Relaxed);
    WORLD_SLOT_ALLOCATED[slot.get() as usize].store(0, Ordering::Relaxed);
}

/// # Safety
/// `slot` is the world slot of the `World` a `GcWorld` scope is opening on, with `&mut` access
/// to it.
pub(crate) unsafe fn enable_gc_borrows(slot: NonZeroU32) {
    // Reset depth before flipping mode so that any leaked ReadWorld depth from a prior
    // GcWorld lifecycle (e.g. via `mem::forget`) cannot poison this fresh slot — otherwise
    // `enter_read_only` would see prev != 0 and skip the GcDynamic -> ReadOnly transition.
    READ_ONLY_DEPTH[slot.get() as usize].store(0, Ordering::Relaxed);
    SLOT_MODE[slot.get() as usize].store(SlotMode::GcDynamic as u8, Ordering::Relaxed);
}

/// # Safety
/// As [`enable_gc_borrows`], at the close of that scope.
pub(crate) unsafe fn disable_gc_borrows(slot: NonZeroU32) {
    // Reset depth as well so a leaked ReadWorld cannot survive past its parent GcWorld.
    READ_ONLY_DEPTH[slot.get() as usize].store(0, Ordering::Relaxed);
    SLOT_MODE[slot.get() as usize].store(SlotMode::Off as u8, Ordering::Relaxed);
}

/// Enter a nested ReadOnly scope on `slot`. Returns the new depth.
/// If the depth transitions from 0 to 1, the slot mode flips to ReadOnly.
///
/// # Safety
/// `slot` belongs to a `World` in a `GcWorld` scope; each call is paired with one
/// [`exit_read_only`] when the `ReadWorld` ends.
pub(crate) unsafe fn enter_read_only(slot: NonZeroU32) -> u32 {
    let prev = READ_ONLY_DEPTH[slot.get() as usize].fetch_add(1, Ordering::Relaxed);
    // Catch silent wrap. With AtomicU32 this is effectively unreachable, but if we ever
    // wrapped, `exit_read_only` would restore `GcDynamic` while scopes are still alive.
    assert!(prev != u32::MAX, "ReadWorld scope nesting overflow");
    if prev == 0 {
        SLOT_MODE[slot.get() as usize].store(SlotMode::ReadOnly as u8, Ordering::Relaxed);
    }
    prev + 1
}

/// Leave a ReadOnly scope on `slot`. When depth returns to 0, mode flips back to GcDynamic.
///
/// # Safety
/// Pairs with an earlier [`enter_read_only`] on the same `slot`.
pub(crate) unsafe fn exit_read_only(slot: NonZeroU32) {
    let prev = READ_ONLY_DEPTH[slot.get() as usize].fetch_sub(1, Ordering::Relaxed);
    debug_assert!(prev > 0, "exit_read_only without matching enter");
    if prev == 1 {
        SLOT_MODE[slot.get() as usize].store(SlotMode::GcDynamic as u8, Ordering::Relaxed);
    }
}

#[cfg(all(debug_assertions, feature = "std"))]
std::thread_local! {
    static POISON: core::cell::Cell<Option<u8>> = const { core::cell::Cell::new(None) };
}

/// Debug builds: while `Some(byte)`, every component value this thread drops or moves out of a
/// slot is overwritten with `byte` afterwards, so a test can check that nothing reads a value
/// after it left its slot (a revive, a restore). `None` turns it off. No effect in release
/// builds.
pub fn debug_poison_vacated(byte: Option<u8>) {
    #[cfg(all(debug_assertions, feature = "std"))]
    POISON.with(|p| p.set(byte));
    #[cfg(not(all(debug_assertions, feature = "std")))]
    let _ = byte;
}

/// [`debug_poison_vacated`]'s write: `size` bytes at `value`, whose value was just dropped or
/// moved out.
#[inline(always)]
fn poison_vacated(value: *mut u8, size: usize) {
    #[cfg(all(debug_assertions, feature = "std"))]
    if let Some(byte) = POISON.with(|p| p.get()) {
        // SAFETY: the slot's value bytes, no longer holding a value nor borrowed.
        unsafe { core::ptr::write_bytes(value, byte, size) };
    }
    #[cfg(not(all(debug_assertions, feature = "std")))]
    let _ = (value, size);
}
/// Per world slot: the parity of the current GC cycle's marks (0 or 1). A cell is marked in
/// this cycle when its mark bit equals it ([`header`]); [`sweep`] flips it at its end.
static MARK_PARITY: [AtomicU8; 256] = [const { AtomicU8::new(0) }; 256];

/// The mark parity of the world in `slot`: what [`GCPtr::mark_referenced`] writes, and what a
/// tombstone written now reads as unmarked under.
#[inline]
pub fn mark_parity(slot: NonZeroU32) -> u32 {
    MARK_PARITY[slot.get() as usize].load(Ordering::Relaxed) as u32
}

fn flip_mark_parity(slot: NonZeroU32) {
    MARK_PARITY[slot.get() as usize].fetch_xor(1, Ordering::Relaxed);
}

