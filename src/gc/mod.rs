mod borrow;
mod gc_world;
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
pub use gc_world::GCWorld;
pub use query::*;

use alloc::boxed::Box;
use alloc::vec::Vec;
use bevy_reflect::{impl_reflect_value, FromReflect, FromType, Reflect, ReflectMut, TypeRegistry};
use hashbrown::HashSet;

use crate::{
    archetype::{StorageHeader, DATA_CHUNK_SIZE_BYTES},
    Component, Entity, TypeInfo, World,
};

use self::borrow::{BorrowFlag, BorrowRef, Ref, RefMut};

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
        assert!(
            self.header_ptr().as_ref().state
                == State::Alive {
                    borrow: Cell::new(0)
                }
        );
        ty.drop_value(self.value_ptr().as_ptr());
        self.header_ptr().as_mut().set_tombstone();
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

    fn resolve_moved(&self) -> Self {
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
            State::Free { .. } | State::Alive { .. } => false,
        }
    }
}

#[derive(PartialEq, Debug)]
#[repr(u8)]
pub(crate) enum State {
    /// Slot is free and available for use
    Free { next_free: Option<GCPtr> },
    /// Slot has been moved elsewhere.
    Moved { new_ptr: GCPtr },
    /// Slot contains a valid value
    Alive { borrow: Cell<BorrowFlag> },
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

impl_reflect_value!(CRef<T: Clone + Component + 'static>());
impl<T: Clone + Component> FromReflect for CRef<T> {
    fn from_reflect(reflect: &dyn Reflect) -> Option<Self> {
        reflect.downcast_ref::<Self>().cloned()
    }
}
impl<T: core::fmt::Debug + Component> core::fmt::Debug for CRef<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!();
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
        if let State::Alive { borrow } = unsafe { &ptr.header_ptr().as_ref().state } {
            let borrow = BorrowRef::new(&borrow).expect("already mutable borrowed");
            Ref {
                borrow,
                value: ptr.value_ptr().cast(),
            }
        } else {
            panic!("Borrowing a deleted component")
        }
    }

    pub fn write(&self) -> RefMut<'_, T> {
        let slot = self.ptr.world_slot();
        assert!(is_gc_borrows_enabled(slot), "gc borrows not enabled");
        let ptr = self.ptr.resolve_moved();
        if let State::Alive { borrow } = unsafe { &ptr.header_ptr().as_ref().state } {
            let borrow = BorrowRef::new(&borrow).expect("already mutable borrowed");
            todo!()
        } else {
            panic!("Borrowing a deleted component")
        }
    }
}

#[derive(Clone)]
struct GCRefTypeData {
    gc_info: unsafe fn(&dyn Reflect) -> Option<(GCPtr, unsafe fn(*mut u8) -> *mut dyn Reflect)>,
}
trait GCRef {
    fn gc_info(&self) -> Option<(GCPtr, unsafe fn(*mut u8) -> *mut dyn Reflect)>;
}
unsafe fn reflect_from_ptr<T: Reflect + 'static>(p: *mut u8) -> *mut dyn Reflect {
    &mut *p.cast::<T>() as &mut dyn Reflect
}
impl<T: Component> GCRef for CRef<T> {
    fn gc_info(&self) -> Option<(GCPtr, unsafe fn(*mut u8) -> *mut dyn Reflect)> {
        Some((
            self.ptr,
            reflect_from_ptr::<T> as unsafe fn(*mut u8) -> *mut dyn Reflect,
        ))
    }
}
impl<T: Component + Clone> FromType<CRef<T>> for GCRefTypeData {
    fn from_type() -> Self {
        Self {
            gc_info: |v| {
                <CRef<T> as GCRef>::gc_info(unsafe {
                    &*(v.as_any() as *const dyn core::any::Any as *const CRef<T>)
                })
            },
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) enum TraversalCommand {
    StructField(usize),
    GCInfoFn(unsafe fn(&dyn Reflect) -> Option<(GCPtr, unsafe fn(*mut u8) -> *mut dyn Reflect)>),
}

pub(crate) fn gc_type_traversal(
    type_registry: &TypeRegistry,
    ty: TypeId,
    out: &mut Vec<TraversalCommand>,
) -> bool {
    let ty_info = type_registry
        .get_type_info(ty)
        .expect("archetype type not registered");

    match ty_info {
        bevy_reflect::TypeInfo::Struct(s) => {
            let mut retval = false;
            for i in 0..s.field_len() {
                let field = s.field_at(i).unwrap();
                out.push(TraversalCommand::StructField(i));
                let has_gc_ptr = gc_type_traversal(type_registry, field.type_id(), out);
                if !has_gc_ptr {
                    out.pop();
                }
                retval |= has_gc_ptr;
            }
            retval
        }
        bevy_reflect::TypeInfo::TupleStruct(_) => todo!(),
        bevy_reflect::TypeInfo::Tuple(_) => todo!(),
        bevy_reflect::TypeInfo::List(_) => todo!(),
        bevy_reflect::TypeInfo::Array(_) => todo!(),
        bevy_reflect::TypeInfo::Map(_) => todo!(),
        bevy_reflect::TypeInfo::Enum(_) => todo!(),
        bevy_reflect::TypeInfo::Value(v) => {
            if let Some(get_gc_info) = type_registry.get_type_data::<GCRefTypeData>(v.type_id()) {
                out.push(TraversalCommand::GCInfoFn(get_gc_info.gc_info));
                true
            } else {
                false
            }
        }
        bevy_reflect::TypeInfo::Dynamic(_) => unimplemented!(),
    }
}

pub unsafe fn trace(
    type_registry: &TypeRegistry,
    world: &mut World,
    entity_roots: impl IntoIterator<Item = Entity>,
    ptr_roots: impl IntoIterator<Item = (GCPtr, TypeInfo)>,
) {
    let mut to_process: Vec<(GCPtr, unsafe fn(*mut u8) -> *mut dyn Reflect)> = Vec::new();
    let mut processed = HashSet::<GCPtr>::new();
    for (ptr, ty) in ptr_roots {
        if processed.insert(ptr) {
            to_process.push((ptr, ty.reflect_from_ptr()));
        }
    }
    for ent in entity_roots {
        if let Ok(entity) = world.entity(ent) {
            unsafe {
                let archetype = entity.archetype();
                for (storage_idx, ty) in archetype.types().iter().enumerate() {
                    let data = archetype.get_data_storage(storage_idx);
                    let gc_ptr = data.get_gc_ptr(entity.index());
                    if processed.insert(gc_ptr) {
                        to_process.push((gc_ptr, ty.reflect_from_ptr()));
                    }
                }
            }
        }
    }
    let mut commands = Vec::new();
    while let Some((mut gc_ptr, ty)) = to_process.pop() {
        gc_ptr.mark_referenced();
        let header = gc_ptr.header_ptr().as_mut();
        match &header.state {
            State::Moved { new_ptr } => {
                if processed.insert(*new_ptr) {
                    to_process.push((*new_ptr, ty));
                }
            }
            State::Alive { .. } => {
                let ptr = &mut *ty(gc_ptr.value_ptr().as_ptr());
                commands.clear();
                gc_type_traversal(type_registry, ptr.type_id(), &mut commands);
                for command in &commands {
                    match command {
                        TraversalCommand::StructField(field_idx) => {
                            if let ReflectMut::Struct(s) = ptr.reflect_mut() {
                                s.field_at(*field_idx);
                            } else {
                                panic!("expected struct when traversing type {:?}", ty);
                            }
                        }
                        TraversalCommand::GCInfoFn(f) => {
                            if let Some((ptr, ty)) = f(ptr) {
                                if processed.insert(ptr) {
                                    to_process.push((ptr, ty));
                                }
                            }
                        }
                    }
                }
            }
            State::Free { .. } => assert!(false, "Pointer to freed memory"),
            State::Dead => {}
        }
    }

    let mut archetype_iter_set = Vec::new();
    for archetype in world.archetypes_mut() {
        archetype_iter_set.clear();
        // prepare iterators for each storage
        for (idx, _) in archetype.types().iter().enumerate() {
            let storage = archetype.get_data_storage(idx);
            archetype_iter_set.push(
                storage
                    .iter_gc_ptr(archetype.allocated_values_nonsync())
                    .into_iter(),
            );
        }
        // check each slot for whether it can be freed or not, by checking each component
        for slot in 0..archetype.allocated_values_nonsync() {
            let mut can_free = true;
            for iter in &mut archetype_iter_set {
                let gc_ptr = iter.next().unwrap();
                can_free &= gc_ptr.can_free();
            }
            if can_free {
                archetype.free_slot(slot);
            }
        }
        // reset referenced flag
        for (idx, _) in archetype.types().iter().enumerate() {
            let storage = archetype.get_data_storage(idx);
            for ptr in storage
                .iter_gc_ptr(archetype.allocated_values_nonsync())
                .into_iter()
            {
                let header = unsafe { &mut *ptr.header_ptr().as_ptr() };
                if header.referenced {
                    header.referenced = false;
                }
            }
        }
    }
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
