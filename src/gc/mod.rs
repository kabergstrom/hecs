mod borrow;
mod gc_world;
#[allow(missing_documentation)]
pub mod kvec;

pub(crate) mod cells;
pub mod query;
use core::{
    any::{Any, TypeId},
    cell::Cell,
    marker::PhantomData,
    mem::MaybeUninit,
    num::NonZeroU32,
    ptr::NonNull,
    sync::atomic::{AtomicU32, AtomicU8, Ordering},
};
pub use gc_world::{GcWorld, GcWorldScope, ReadWorld};
pub use query::*;

use self::borrow::{BorrowFlag, BorrowRef, BorrowRefMut, Ref, RefMut};
use crate::{
    archetype::{Archetype, StorageHeader, DATA_CHUNK_SIZE_BYTES},
    Component, Entity, StableTypeId, TypeInfo, World,
};
use alloc::vec::Vec;

/// A pointer to the value of one component slot in a [`World`]'s column storage.
///
/// The slot's [`GCHeader`] sits immediately before the value, and the chunk's storage header
/// at the start of the `DATA_CHUNK_SIZE_BYTES`-aligned chunk the value lives in. The safe
/// methods (`header_ptr`, `world_slot`, `archetype_slot`, `archetype`, `resolve_moved`) read
/// those headers. They are sound because a `GCPtr` is only ever made by hecs from a slot of a
/// live chunk, or through [`GCPtr::from_raw`], whose contract requires the same.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[repr(transparent)]
pub struct GCPtr {
    value: NonNull<u8>,
}
// SAFETY: a `GCPtr` is `Send + Sync` so that `CRef<T>`, and the components holding one, meet
// `Component: Send + Sync`. Nothing reachable through it is synchronized: the slot header's
// borrow flag is a `Cell`, and its state and `referenced` fields are written without atomics.
// It is sound only under the engine's invariant that module code, and every touch of a slot
// (deref, `CRef::read`/`write`, `mark_referenced`, `resolve_moved`, `gc::sweep`), runs on the
// thread that owns the `World`. Modules are `no_std` and cannot spawn threads. What would
// break the invariant, and must not be added without first making the headers atomic: running
// module type-op or VFX thunks on worker threads, or parallel physics with module callbacks.
unsafe impl Send for GCPtr {}
// SAFETY: see the `Send` impl above.
unsafe impl Sync for GCPtr {}
impl GCPtr {
    /// Wrap a slot's value pointer.
    ///
    /// # Safety
    /// `value` must be the value pointer of a slot in a still-allocated chunk of a live
    /// [`World`] (any [`State`]; the world's [dead slot](World::dead_gc_ptr) counts), and that
    /// `World` must outlive every use of the returned `GCPtr` and of its copies: the safe
    /// methods dereference the slot and chunk headers through it. A placeholder that breaks
    /// this is allowed only if no method is called on it and it is never turned into a `CRef`.
    #[inline]
    pub const unsafe fn from_raw(value: NonNull<u8>) -> Self {
        Self { value }
    }

    /// The slot's value pointer (same as [`value_ptr`](Self::value_ptr)).
    #[inline]
    pub const fn value(&self) -> NonNull<u8> {
        self.value
    }

    pub fn header_ptr(&self) -> NonNull<GCHeader> {
        // The header precedes the value inside the chunk, so this stays in bounds for any
        // `GCPtr` that meets `from_raw`'s contract. `wrapping_sub` keeps computing the address
        // free of UB even for a misused placeholder.
        let header = self
            .value
            .as_ptr()
            .wrapping_sub(core::mem::size_of::<GCHeader>());
        assert!(header as usize % core::mem::align_of::<GCHeader>() == 0);
        // SAFETY: the value lies at least `size_of::<GCHeader>()` past its chunk's start, so
        // the header address is non-null.
        unsafe { NonNull::new_unchecked(header.cast()) }
    }
    pub(crate) fn storage_header(&self) -> *const StorageHeader {
        let storage_header_addr = self.value.as_ptr() as usize;
        let diff = storage_header_addr % DATA_CHUNK_SIZE_BYTES;
        self.value
            .as_ptr()
            .wrapping_sub(diff)
            .cast::<StorageHeader>()
    }
    pub fn world_slot(&self) -> NonZeroU32 {
        unsafe { (&*self.storage_header()).world_slot }
    }
    pub fn archetype_slot(&self) -> u32 {
        let storage_header_ptr = self.storage_header();
        let storage_header = unsafe { &*storage_header_ptr };
        let entities_per_chunk =
            (DATA_CHUNK_SIZE_BYTES - storage_header.data_start) / storage_header.stride;
        let chunk_slot_start = storage_header.chunk_idx * entities_per_chunk;
        let byte_diff = unsafe {
            let chunk_data_start = storage_header_ptr
                .cast::<u8>()
                .add(storage_header.data_start);
            self.header_ptr()
                .as_ptr()
                .cast::<u8>()
                .offset_from(chunk_data_start)
        };
        debug_assert!(
            byte_diff >= 0 && byte_diff as usize / storage_header.stride < entities_per_chunk
        );
        (chunk_slot_start + (byte_diff as usize / storage_header.stride)) as u32
    }
    pub fn value_ptr(&self) -> NonNull<u8> {
        self.value
    }

    /// Returns a raw pointer to the owning archetype.
    ///
    /// The back-pointer is written when the chunk is allocated and remains
    /// valid for the lifetime of the archetype, which equals the lifetime of
    /// the owning `World`. Callers must not outlive the `World`.
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

    // pub unsafe fn drop(&mut self, ty: &TypeInfo) {
    //     self.header_ptr().as_ptr().drop_in_place();
    //     ty.drop_value(self.value_ptr().as_ptr());
    // }
    /// The `GCPtr` of the slot that starts at `base`, whose value lies `data_start` bytes in.
    ///
    /// # Safety
    /// `base` is the start of a slot (where its [`GCHeader`] storage begins) in a
    /// still-allocated chunk of a live `World`, and `data_start` is that column's value offset
    /// ([`Data::value_start`](crate::Data::value_start), i.e. [`TypeInfo::data_start`]). The
    /// result must then meet [`from_raw`](Self::from_raw)'s contract.
    pub unsafe fn from_base_with_offset(data_start: usize, base: NonNull<u8>) -> Self {
        Self {
            value: NonNull::new_unchecked(base.as_ptr().add(data_start)),
        }
    }
    /// The `GCPtr` of the slot of a `ty` column that starts at `base`.
    ///
    /// # Safety
    /// As [`from_base_with_offset`](Self::from_base_with_offset), with `ty` the column's type.
    pub unsafe fn from_base(ty: &TypeInfo, base: NonNull<u8>) -> Self {
        Self {
            value: NonNull::new_unchecked(base.as_ptr().add(ty.data_start())),
        }
    }

    /// The slot header's `state`, projected through raw pointers. Header writes go through
    /// this (and [`referenced_ptr`](Self::referenced_ptr)) rather than a `&mut GCHeader`,
    /// because a gc borrow guard holds a `&Cell` to the borrow flag inside `state`, which a
    /// `&mut GCHeader` would alias.
    #[inline]
    pub(crate) fn state_ptr(&self) -> *mut State {
        // SAFETY: the header is in bounds of the slot (from_raw's contract); `addr_of_mut!`
        // makes no reference.
        unsafe { core::ptr::addr_of_mut!((*self.header_ptr().as_ptr()).state) }
    }

    /// The slot header's `referenced` flag; see [`state_ptr`](Self::state_ptr).
    #[inline]
    fn referenced_ptr(&self) -> *mut bool {
        // SAFETY: as `state_ptr`.
        unsafe { core::ptr::addr_of_mut!((*self.header_ptr().as_ptr()).referenced) }
    }

    /// Whether the slot is `Alive`, not pending dead, and free of gc borrow guards: the only
    /// state in which its value may be moved out (`move_from`, `migrate_from`,
    /// `mark_tombstone`). Insert and remove check every slot they would move with this before
    /// changing anything.
    #[inline]
    pub(crate) fn is_movable(&self) -> bool {
        // SAFETY: a short shared `&State` may coexist with a guard's `&Cell` (the flag is
        // interior-mutable); the slot is valid by from_raw's contract.
        matches!(
            unsafe { &*self.state_ptr() },
            State::Alive { borrow, pending_dead: false } if borrow.get() == 0
        )
    }

    /// Set the slot's state to `Dead` without dropping its value; the caller has taken (or
    /// will take) ownership of the value.
    ///
    /// # Safety
    /// - NS.
    /// - The slot is movable: `Alive`, not pending dead, with no gc borrow guard (`CRef`
    ///   `Ref`/`RefMut`) held on it. A guard keeps a `&Cell` to the borrow flag, which this
    ///   overwrites. Only debug-checked: callers refuse the operation beforehand.
    /// - No column borrows on it, and no `&T`/`&mut T` into the value used afterwards.
    /// - The value is moved out exactly once (or deliberately leaked), never dropped in place.
    pub unsafe fn mark_tombstone(&mut self) {
        debug_assert!(self.is_movable(), "tombstoning a borrowed or dead slot");
        self.state_ptr().write(State::Dead);
    }

    /// Hand the value to `f` (pointer plus type, for it to move out) and set the slot `Dead`.
    ///
    /// # Safety
    /// As [`mark_tombstone`](Self::mark_tombstone) (the slot is movable: its only caller,
    /// [`TakenEntity`](crate::TakenEntity), comes from [`World::take`](crate::World::take),
    /// which refuses a row with a borrowed slot), and `ty` is the slot's column type. `f` must
    /// move the value out (or leak it); the slot never drops it.
    pub unsafe fn move_value_and_tombstone(
        &mut self,
        ty: &TypeInfo,
        mut f: impl FnMut(*mut u8, TypeInfo),
    ) {
        f(self.value_ptr().as_ptr(), ty.clone());
        self.state_ptr().write(State::Dead);
    }
    /// Mark this slot referenced so tombstone sweep spares it. Propagates
    /// along the `Moved` forwarding chain: a referenced tombstone is only
    /// resolvable if every intermediate hop survives the sweep too.
    ///
    /// # Safety
    /// - NS, and no `gc::sweep` runs concurrently.
    /// - Every slot on the `Moved` chain is in a still-allocated chunk: no sweep has freed a
    ///   hop since this `GCPtr` was last known to reach a referenced slot. (Callers mark from
    ///   roots during a mark phase, before the sweep that would free unmarked hops.)
    pub unsafe fn mark_referenced(&mut self) {
        let mut ptr = *self;
        loop {
            ptr.referenced_ptr().write(true);
            match &*ptr.state_ptr() {
                State::Moved { new_ptr } => ptr = *new_ptr,
                _ => break,
            }
        }
    }
    /// Drop the slot's value and set it `Dead`, or, if a gc borrow guard is held on it, set
    /// `pending_dead` so the first `gc::sweep` after the last guard goes drops it.
    ///
    /// # Safety
    /// - NS.
    /// - The slot is `Alive` (else this panics), and `ty` is its column type.
    /// - No column borrows on it, and no `&T`/`&mut T` into the value (other than through a
    ///   gc guard, which the `pending_dead` path keeps valid) is used afterwards.
    pub unsafe fn drop_value_and_tombstone(&mut self, ty: &TypeInfo) {
        let state = self.state_ptr();
        let borrowed = match &*state {
            State::Alive { borrow, .. } => borrow.get() != 0,
            other => panic!("unexpected state when dropping value: {:?}", other),
        };
        if !borrowed {
            ty.drop_value(self.value_ptr().as_ptr());
            poison_vacated(self.value_ptr().as_ptr(), ty.value_layout().size());
            state.write(State::Dead);
        } else {
            // Write only the flag's byte: the guard's `&Cell` covers the borrow flag next to it.
            state
                .cast::<u8>()
                .add(core::mem::offset_of!(AliveRepr, pending_dead))
                .cast::<bool>()
                .write(true);
        }
    }
    /// Move `value` (a `ty`, bitwise) into this free slot and make it `Alive`. The caller must
    /// not use or drop `value` afterwards.
    ///
    /// # Safety
    /// NS; the slot is `Free` (asserted) and of a `ty` column; `value` points to a valid `ty`
    /// that does not overlap the slot.
    pub unsafe fn move_from_value(&mut self, ty: &TypeInfo, value: *mut u8) {
        let dst_header = self.header_ptr().as_ptr();
        assert!(matches!(&*self.state_ptr(), State::Free { .. }));
        dst_header.write(GCHeader::new_alive());
        core::ptr::copy_nonoverlapping(value, self.value_ptr().as_ptr(), ty.value_layout().size());
    }

    /// Move `src`'s value (a `ty`, bitwise) into this free slot; `src` becomes a `Moved`
    /// tombstone forwarding here.
    ///
    /// # Safety
    /// NS; this slot is `Free` and of a `ty` column; `src` is a different, movable slot
    /// ([`is_movable`](Self::is_movable)) of a `ty` column, checked by the caller before the
    /// operation began (only debug-asserted here); no column borrows on `src`.
    pub(crate) unsafe fn move_from(&mut self, ty: &TypeInfo, src: GCPtr) {
        debug_assert!(src != *self);
        debug_assert!(matches!(&*self.state_ptr(), State::Free { .. }));
        // Need source to be alive with no active borrows: callers check before they start.
        debug_assert!(src.is_movable(), "moving a borrowed or dead slot");
        self.state_ptr().write(State::Alive {
            borrow: Cell::new(0),
            pending_dead: false,
        });
        src.state_ptr().write(State::Moved { new_ptr: *self });
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
    /// As [`move_from`](Self::move_from), with `f` initializing a valid value of this slot's
    /// column type from `src`'s.
    pub(crate) unsafe fn migrate_from(&mut self, src: GCPtr, f: impl FnOnce(*mut u8, *mut u8)) {
        debug_assert!(src != *self);
        debug_assert!(matches!(&*self.state_ptr(), State::Free { .. }));
        debug_assert!(src.is_movable(), "migrating a borrowed or dead slot");
        self.state_ptr().write(State::Alive {
            borrow: Cell::new(0),
            pending_dead: false,
        });
        src.state_ptr().write(State::Moved { new_ptr: *self });
        f(src.value_ptr().as_ptr(), self.value_ptr().as_ptr());
    }

    pub fn resolve_moved(&self) -> Self {
        let mut ptr = *self;
        while let State::Moved { new_ptr } = unsafe { ptr.header_ptr().as_ref() }.state {
            ptr = new_ptr;
        }
        ptr
    }

    fn can_free(&self) -> bool {
        let header = unsafe { &*self.header_ptr().as_ptr() };
        match header.state {
            State::Dead => !header.referenced,
            State::Moved { .. } => !header.referenced,
            State::Free { .. } | State::Alive { .. } => false,
        }
    }
}

/// The layout of [`State::Alive`]: `#[repr(u8)]` lays each variant out as a `#[repr(C)]`
/// struct led by the `u8` tag (RFC 2195). Lets `drop_value_and_tombstone` write the
/// `pending_dead` byte alone, beside a guard's `&Cell` to `borrow`.
#[repr(C)]
struct AliveRepr {
    tag: u8,
    borrow: Cell<BorrowFlag>,
    pending_dead: bool,
}

#[derive(PartialEq, Debug)]
#[repr(u8)]
pub enum State {
    /// Slot is free and available for use
    Free { next_free: Option<GCPtr> },
    /// Slot has been moved elsewhere.
    Moved { new_ptr: GCPtr },
    /// Slot contains a valid value
    Alive {
        borrow: Cell<BorrowFlag>,
        /// Borrows exist, and the value should be dropped when the last active
        /// borrow expires.
        pending_dead: bool,
    },
    /// Slot does not contain a valid value, but references may exist to it so it cannot be reused.
    Dead,
}
impl Default for State {
    fn default() -> Self {
        Self::Free { next_free: None }
    }
}
// GCHeader is stored tightly packed before the value in memory.
// When the alignment requirements of the value is larger than the size of GCHeader,
// bytes up to the value address minus the size of GCHeader are unused.
#[derive(Default)]
pub struct GCHeader {
    pub(crate) referenced: bool,
    pub(crate) state: State,
}
impl GCHeader {
    pub fn new_alive() -> Self {
        Self {
            state: State::Alive {
                borrow: Cell::new(0),
                pending_dead: false,
            },
            referenced: false,
        }
    }
    pub fn set_tombstone(&mut self) {
        self.state = State::Dead;
    }
    /// Returns true if this slot is in the Alive state.
    pub fn is_alive(&self) -> bool {
        matches!(self.state, State::Alive { .. })
    }
    /// Returns true if this slot is Alive and not pending-dead — the same
    /// liveness predicate `CRef` uses before dereferencing.
    pub fn is_live(&self) -> bool {
        matches!(
            self.state,
            State::Alive {
                pending_dead: false,
                ..
            }
        )
    }
    /// Diagnostic name of the slot state, for resolve-failure logging.
    pub fn state_name(&self) -> &'static str {
        match self.state {
            State::Free { .. } => "Free",
            State::Moved { .. } => "Moved",
            State::Alive {
                pending_dead: false,
                ..
            } => "Alive",
            State::Alive { .. } => "AlivePendingDead",
            State::Dead => "Dead",
        }
    }
}
impl<T: Component + core::fmt::Debug> core::fmt::Debug for GC<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

#[repr(C)]
pub struct GC<T> {
    pub(crate) header_storage: MaybeUninit<GCHeader>,
    pub(crate) value: T,
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
    fn live_ptr(&self) -> Option<GCPtr> {
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if !matches!(
            header.state,
            State::Alive {
                pending_dead: false,
                ..
            }
        ) {
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
    pub fn read(&self) -> Ref<'_, T> {
        let slot = self.ptr.world_slot();
        match slot_mode(slot) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::GcDynamic | SlotMode::ReadOnly => {}
        }
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive {
            borrow,
            pending_dead: false,
        } = &header.state
        {
            let borrow = BorrowRef::new(borrow).expect("already mutably borrowed");
            Ref {
                value: ptr.value_ptr().cast(),
                borrow,
            }
        } else {
            panic!("Borrowing a deleted component")
        }
    }

    pub fn try_read(&self) -> Option<Ref<'_, T>> {
        let slot = self.ptr.world_slot();
        match slot_mode(slot) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::GcDynamic | SlotMode::ReadOnly => {}
        }
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive {
            borrow,
            pending_dead: false,
        } = &header.state
        {
            let borrow = BorrowRef::new(borrow)?;
            Some(Ref {
                value: ptr.value_ptr().cast(),
                borrow,
            })
        } else {
            None
        }
    }

    pub fn write(&self) -> RefMut<'_, T> {
        match slot_mode(self.ptr.world_slot()) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::ReadOnly => panic!("CRef::write during ReadWorld scope"),
            SlotMode::GcDynamic => {}
        }
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive {
            borrow,
            pending_dead: false,
        } = &header.state
        {
            let borrow = BorrowRefMut::new(borrow).expect("already borrowed");
            RefMut {
                value: ptr.value_ptr().cast(),
                borrow,
                marker: Default::default(),
            }
        } else {
            panic!("Borrowing a deleted component")
        }
    }
    pub fn try_write(&self) -> Option<RefMut<'_, T>> {
        match slot_mode(self.ptr.world_slot()) {
            SlotMode::Off => panic!("gc borrows not enabled"),
            SlotMode::ReadOnly => panic!("CRef::try_write during ReadWorld scope"),
            SlotMode::GcDynamic => {}
        }
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive {
            borrow,
            pending_dead: false,
        } = &header.state
        {
            let borrow = BorrowRefMut::new(borrow)?;
            Some(RefMut {
                value: ptr.value_ptr().cast(),
                borrow,
                marker: Default::default(),
            })
        } else {
            None
        }
    }

    /// Cheap, lifetime-bound deref valid only while a [`ReadWorld`] scope is active.
    ///
    /// # Why this is faster than [`read`](Self::read)
    ///
    /// The dynamic path ([`read`](Self::read)) does, on every call:
    /// - an atomic load of the per-slot mode flag,
    /// - a load + branch + **store** on the per-component borrow counter (cell increment),
    /// - constructs a `Ref<'_, T>` whose `Drop` does another load + branch + store
    ///   (cell decrement) and a pending-dead state check.
    ///
    /// `read_bypass` does, on every call:
    /// - a load + branch on the borrow counter (to reject if a `RefMut` is held),
    /// - a pointer cast to `&T`.
    ///
    /// In raw cycles the saved work is small (~7–12 cycles per access). The bigger
    /// wins are second-order: no writes to the borrow cell means the cache line stays
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
    /// 3. The `borrow.get() >= 0` check rejects calls made while a `RefMut` is held
    ///    (which could pre-date the scope, since the scope can't retroactively cancel
    ///    an outstanding mutable borrow). Without this check, `&mut T` and `&T` could
    ///    coexist in safe code.
    pub fn read_bypass<'s>(&self, scope: &'s ReadWorld<'_>) -> &'s T {
        assert_eq!(
            self.ptr.world_slot(),
            scope.world_slot(),
            "CRef belongs to a different World than the ReadWorld scope"
        );
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        let State::Alive {
            borrow,
            pending_dead: false,
        } = &header.state
        else {
            panic!("Borrowing a deleted component")
        };
        assert!(
            borrow.get() >= 0,
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
    /// 3. The component has not been despawned and is still in [`State::Alive`]
    ///    with `pending_dead == false`.
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

/// Sweep tombstones from the world, freeing slots where all components are
/// Dead/Moved and not marked as referenced, counting each free in the row's
/// [`row_generation`](crate::Archetype::row_generation). Resets all `referenced` flags.
///
/// Nothing else keeps a tombstone: copies of slot memory that may point at one (rollback
/// history) must be traced as roots, so that it is marked.
///
/// Call this after marking live slots with `GCPtr::mark_referenced()`.
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
    let mut freed = 0u32;
    let mut archetype_iter_set = Vec::new();
    for (_, archetype) in world.archetypes() {
        let count = archetype.allocated_values_nonsync();
        archetype_iter_set.clear();
        for (idx, ty) in archetype.types().iter().enumerate() {
            let storage = archetype.get_data_storage(idx);
            archetype_iter_set.push((ty, storage.iter_gc_ptr(count).into_iter()));
        }
        for slot in 0..count {
            let mut can_free = true;
            for (ty, iter) in &mut archetype_iter_set {
                let gc_ptr = iter.next().unwrap();
                // Raw projections, not `&mut GCHeader`: a guard may still hold a `&Cell` into
                // a pending-dead slot's header.
                let state = gc_ptr.state_ptr();
                let referenced = gc_ptr.referenced_ptr();
                let freeable = match &*state {
                    State::Alive {
                        borrow,
                        pending_dead: true,
                    } => {
                        if borrow.get() == 0 {
                            ty.drop_value(gc_ptr.value_ptr().as_ptr());
                            poison_vacated(gc_ptr.value_ptr().as_ptr(), ty.value_layout().size());
                            state.write(State::Dead);
                            !referenced.read()
                        } else {
                            false
                        }
                    }
                    // Inline can_free logic — header already dereferenced
                    State::Dead | State::Moved { .. } => !referenced.read(),
                    _ => false,
                };
                // Reset referenced flag in the same pass
                referenced.write(false);
                can_free &= freeable;
            }
            if can_free {
                archetype.free_slot(slot);
                freed += 1;
            }
        }
    }
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
    static POISON: Cell<Option<u8>> = const { Cell::new(None) };
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
