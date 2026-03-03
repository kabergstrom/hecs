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
    sync::atomic::{AtomicBool, Ordering},
};
pub use gc_world::{GcWorld, GcWorldScope};
pub use query::*;

use crate::{
    archetype::{StorageHeader, DATA_CHUNK_SIZE_BYTES},
    Component, TypeInfo, World,
};
use alloc::vec::Vec;
use self::borrow::{BorrowFlag, BorrowRef, BorrowRefMut, Ref, RefMut};

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
        match self.header_ptr().as_ref().state {
            State::Alive { ref borrow, .. } => {
                if borrow.get() == 0 {
                    ty.drop_value(self.value_ptr().as_ptr());
                    self.header_ptr().as_mut().set_tombstone();
                } else {
                    self.header_ptr().as_mut().state = State::PendingDead;
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
                    borrow: Cell::new(0)
                }
        );
        dst_header.state = State::Alive {
            borrow: Cell::new(0),
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
        while let State::Moved { new_ptr } = unsafe { self.header_ptr().as_ref() }.state {
            ptr = new_ptr;
        }
        ptr
    }

    fn can_free(&self) -> bool {
        let header = unsafe { &*self.header_ptr().as_ptr() };
        match header.state {
            State::Dead => !header.referenced,
            State::Moved { .. } => !header.referenced,
            State::Free { .. } | State::Alive { .. } | State::PendingDead => false,
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
    Alive { borrow: Cell<BorrowFlag> },
    /// Slot contains a valid value, but borrows exist so the value will be dropped when all active borrows expire
    PendingDead,
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
    pub fn ptr_eq(&self, other: &Self) -> bool {
        let a = self.ptr.resolve_moved();
        let b = other.ptr.resolve_moved();
        a == b
    }
    pub fn read(&self) -> Ref<'_, T> {
        let slot = self.ptr.world_slot();
        assert!(is_gc_borrows_enabled(slot), "gc borrows not enabled");
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive { borrow } = &header.state {
            let borrow = BorrowRef::new(&borrow).expect("already mutable borrowed");
            Ref {
                borrow,
                state: unsafe {
                    NonNull::new_unchecked(core::ptr::addr_of!(header.state).cast_mut())
                },
                value: ptr.value_ptr().cast(),
            }
        } else {
            panic!("Borrowing a deleted component")
        }
    }

    pub fn try_read(&self) -> Option<Ref<'_, T>> {
        let slot = self.ptr.world_slot();
        assert!(is_gc_borrows_enabled(slot), "gc borrows not enabled");
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive { borrow } = &header.state {
            let borrow = BorrowRef::new(&borrow).expect("already mutable borrowed");
            Some(Ref {
                borrow,
                state: unsafe {
                    NonNull::new_unchecked(core::ptr::addr_of!(header.state).cast_mut())
                },
                value: ptr.value_ptr().cast(),
            })
        } else {
            None
        }
    }

    pub fn write(&self) -> RefMut<'_, T> {
        let slot = self.ptr.world_slot();
        assert!(is_gc_borrows_enabled(slot), "gc borrows not enabled");
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive { borrow } = &header.state {
            let borrow = BorrowRefMut::new(&borrow).expect("already mutable borrowed");
            RefMut {
                borrow,
                state: unsafe {
                    NonNull::new_unchecked(core::ptr::addr_of!(header.state).cast_mut())
                },
                value: ptr.value_ptr().cast(),
                marker: Default::default(),
            }
        } else {
            panic!("Borrowing a deleted component")
        }
    }
    pub fn try_write(&self) -> Option<RefMut<'_, T>> {
        let slot = self.ptr.world_slot();
        assert!(is_gc_borrows_enabled(slot), "gc borrows not enabled");
        let ptr = self.ptr.resolve_moved();
        let header = unsafe { ptr.header_ptr().as_ref() };
        if let State::Alive { borrow } = &header.state {
            let borrow = BorrowRefMut::new(&borrow).expect("already mutable borrowed");
            Some(RefMut {
                borrow,
                state: unsafe {
                    NonNull::new_unchecked(core::ptr::addr_of!(header.state).cast_mut())
                },
                value: ptr.value_ptr().cast(),
                marker: Default::default(),
            })
        } else {
            None
        }
    }
}


/// Sweep tombstones from the world, freeing slots where all components are
/// Dead/Moved and not marked as referenced. Resets all `referenced` flags.
///
/// Call this after marking live slots with `GCPtr::mark_referenced()`.
/// Returns the number of entity slots freed.
///
/// # Safety
/// Must not be called while any GcWorld scope is active or while component
/// borrows are held.
pub unsafe fn sweep(world: &World) -> u32 {
    let mut freed = 0u32;
    let mut archetype_iter_set = Vec::new();
    for (_, archetype) in world.archetypes() {
        let count = archetype.allocated_values_nonsync();
        archetype_iter_set.clear();
        for (idx, _) in archetype.types().iter().enumerate() {
            let storage = archetype.get_data_storage(idx);
            archetype_iter_set.push(
                storage
                    .iter_gc_ptr(count)
                    .into_iter(),
            );
        }
        for slot in 0..count {
            let mut can_free = true;
            for iter in &mut archetype_iter_set {
                let gc_ptr = iter.next().unwrap();
                can_free &= gc_ptr.can_free();
            }
            if can_free {
                archetype.free_slot(slot);
                freed += 1;
            }
        }
        // Reset referenced flags
        for (idx, _) in archetype.types().iter().enumerate() {
            let storage = archetype.get_data_storage(idx);
            for ptr in storage
                .iter_gc_ptr(count)
                .into_iter()
            {
                let header = &mut *ptr.header_ptr().as_ptr();
                if header.referenced {
                    header.referenced = false;
                }
            }
        }
    }
    freed
}

const FALSE_BOOL: AtomicBool = AtomicBool::new(false);
static BORROWS_ENABLED: [AtomicBool; 256] = [FALSE_BOOL; 256];
static WORLD_SLOT_ALLOCATED: [AtomicBool; 256] = [FALSE_BOOL; 256];

fn is_gc_borrows_enabled(slot: NonZeroU32) -> bool {
    BORROWS_ENABLED[slot.get() as usize].load(Ordering::Relaxed)
}

pub(crate) fn alloc_world_slot() -> NonZeroU32 {
    for i in 1..WORLD_SLOT_ALLOCATED.len() {
        if let Ok(_) = WORLD_SLOT_ALLOCATED[i].compare_exchange(
            false,
            true,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            return NonZeroU32::new(i as u32).unwrap();
        }
    }
    panic!("max 256 worlds active concurrently")
}

pub(crate) unsafe fn free_world_slot(slot: NonZeroU32) {
    WORLD_SLOT_ALLOCATED[slot.get() as usize].store(false, Ordering::Relaxed)
}

pub(crate) unsafe fn enable_gc_borrows(slot: NonZeroU32) {
    BORROWS_ENABLED[slot.get() as usize].store(true, Ordering::Relaxed)
}

pub(crate) unsafe fn disable_gc_borrows(slot: NonZeroU32) {
    BORROWS_ENABLED[slot.get() as usize].store(false, Ordering::Relaxed)
}
