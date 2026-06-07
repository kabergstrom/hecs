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

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[repr(transparent)]
pub struct GCPtr {
    pub value: NonNull<u8>,
}
unsafe impl Send for GCPtr {}
unsafe impl Sync for GCPtr {}
impl GCPtr {
    pub fn header_ptr(&self) -> NonNull<GCHeader> {
        unsafe {
            assert!(
                self.value.as_ptr().sub(core::mem::size_of::<GCHeader>()) as usize
                    % (core::alloc::Layout::new::<GCHeader>().align())
                    == 0
            );
            NonNull::new_unchecked(
                self.value
                    .as_ptr()
                    .sub(core::mem::size_of::<GCHeader>())
                    .cast(),
            )
        }
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

    /// Returns the [`Entity`] associated with this slot.
    ///
    /// # Safety
    /// The owning `World` must still be alive.
    pub unsafe fn entity(&self) -> Entity {
        (*self.archetype()).entity(self.archetype_slot())
    }

    /// Returns a `GCPtr` to the sibling component of type `id` belonging to
    /// the same entity, or `None` if the archetype does not contain that
    /// component.
    ///
    /// # Safety
    /// The owning `World` must still be alive.
    pub unsafe fn sibling_by_id(&self, id: StableTypeId) -> Option<GCPtr> {
        (*self.archetype()).get_dynamic_by_id(id, self.archetype_slot())
    }

    /// Returns a `GCPtr` to the sibling component of type `T` belonging to
    /// the same entity, or `None` if the archetype does not contain `T`.
    ///
    /// # Safety
    /// The owning `World` must still be alive.
    pub unsafe fn sibling<T: Component>(&self) -> Option<GCPtr> {
        self.sibling_by_id(T::STABLE_TYPE_ID)
    }

    // pub unsafe fn drop(&mut self, ty: &TypeInfo) {
    //     self.header_ptr().as_ptr().drop_in_place();
    //     ty.drop_value(self.value_ptr().as_ptr());
    // }
    pub unsafe fn from_base_with_offset(data_start: usize, base: NonNull<u8>) -> Self {
        Self {
            value: NonNull::new_unchecked(base.as_ptr().add(data_start)),
        }
    }
    pub unsafe fn from_base(ty: &TypeInfo, base: NonNull<u8>) -> Self {
        Self {
            value: NonNull::new_unchecked(base.as_ptr().add(ty.data_start())),
        }
    }

    pub unsafe fn mark_tombstone(&mut self) {
        self.header_ptr().as_mut().set_tombstone();
    }

    pub unsafe fn move_value_and_tombstone(
        &mut self,
        ty: &TypeInfo,
        mut f: impl FnMut(*mut u8, TypeInfo),
    ) {
        f(self.value_ptr().as_ptr(), ty.clone());
        self.header_ptr().as_mut().set_tombstone();
    }
    pub unsafe fn mark_referenced(&mut self) {
        self.header_ptr().as_mut().referenced = true;
    }
    pub unsafe fn drop_value_and_tombstone(&mut self, ty: &TypeInfo) {
        let header = self.header_ptr().as_mut();
        match &mut header.state {
            State::Alive {
                borrow,
                pending_dead,
            } => {
                if borrow.get() == 0 {
                    ty.drop_value(self.value_ptr().as_ptr());
                    header.set_tombstone();
                } else {
                    *pending_dead = true;
                }
            }
            ref state => {
                panic!("unexpected state when dropping value: {:?}", state)
            }
        }
    }
    pub unsafe fn move_from_value(&mut self, ty: &TypeInfo, value: *mut u8) {
        let dst_header = self.header_ptr().as_ptr();
        assert!(matches!(dst_header.read().state, State::Free { .. }));
        dst_header.write(GCHeader::new_alive());
        core::ptr::copy_nonoverlapping(value, self.value_ptr().as_ptr(), ty.value_layout().size());
    }

    pub(crate) unsafe fn move_from(&mut self, ty: &TypeInfo, src: GCPtr) {
        assert!(src != *self);
        let dst_header = self.header_ptr().as_mut();
        assert!(matches!(dst_header.state, State::Free { .. }));
        let src_header = src.header_ptr().as_mut();
        // Need source to be alive with no active borrows
        assert!(
            src_header.state
                == State::Alive {
                    borrow: Cell::new(0),
                    pending_dead: false,
                }
        );
        dst_header.state = State::Alive {
            borrow: Cell::new(0),
            pending_dead: false,
        };
        src_header.state = State::Moved { new_ptr: *self };
        core::ptr::copy_nonoverlapping(
            src.value_ptr().as_ptr(),
            self.value_ptr().as_ptr(),
            ty.value_layout().size(),
        );
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
/// Dead/Moved and not marked as referenced. Resets all `referenced` flags.
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
                let header = &mut *gc_ptr.header_ptr().as_ptr();
                let freeable = match &mut header.state {
                    State::Alive {
                        borrow,
                        pending_dead: true,
                    } => {
                        if borrow.get() == 0 {
                            ty.drop_value(gc_ptr.value_ptr().as_ptr());
                            header.set_tombstone();
                            !header.referenced
                        } else {
                            false
                        }
                    }
                    // Inline can_free logic — header already dereferenced
                    State::Dead | State::Moved { .. } => !header.referenced,
                    _ => false,
                };
                // Reset referenced flag in the same pass
                header.referenced = false;
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

pub(crate) unsafe fn free_world_slot(slot: NonZeroU32) {
    // Defensive: ensure a freed slot can't leak GcDynamic/ReadOnly into its next user.
    SLOT_MODE[slot.get() as usize].store(SlotMode::Off as u8, Ordering::Relaxed);
    READ_ONLY_DEPTH[slot.get() as usize].store(0, Ordering::Relaxed);
    WORLD_SLOT_ALLOCATED[slot.get() as usize].store(0, Ordering::Relaxed);
}

pub(crate) unsafe fn enable_gc_borrows(slot: NonZeroU32) {
    // Reset depth before flipping mode so that any leaked ReadWorld depth from a prior
    // GcWorld lifecycle (e.g. via `mem::forget`) cannot poison this fresh slot — otherwise
    // `enter_read_only` would see prev != 0 and skip the GcDynamic -> ReadOnly transition.
    READ_ONLY_DEPTH[slot.get() as usize].store(0, Ordering::Relaxed);
    SLOT_MODE[slot.get() as usize].store(SlotMode::GcDynamic as u8, Ordering::Relaxed);
}

pub(crate) unsafe fn disable_gc_borrows(slot: NonZeroU32) {
    // Reset depth as well so a leaked ReadWorld cannot survive past its parent GcWorld.
    READ_ONLY_DEPTH[slot.get() as usize].store(0, Ordering::Relaxed);
    SLOT_MODE[slot.get() as usize].store(SlotMode::Off as u8, Ordering::Relaxed);
}

/// Enter a nested ReadOnly scope on `slot`. Returns the new depth.
/// If the depth transitions from 0 to 1, the slot mode flips to ReadOnly.
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
pub(crate) unsafe fn exit_read_only(slot: NonZeroU32) {
    let prev = READ_ONLY_DEPTH[slot.get() as usize].fetch_sub(1, Ordering::Relaxed);
    debug_assert!(prev > 0, "exit_read_only without matching enter");
    if prev == 1 {
        SLOT_MODE[slot.get() as usize].store(SlotMode::GcDynamic as u8, Ordering::Relaxed);
    }
}
