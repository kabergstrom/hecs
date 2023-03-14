// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::alloc::alloc::{alloc, dealloc, Layout};
use crate::alloc::boxed::Box;
use crate::alloc::{vec, vec::Vec};
use crate::gc::cells::{PtrCell, U32Cell};
use crate::gc::kvec::KVec;
use crate::gc::{GCHeader, GCPtr, TraversalCommand, GC};
use core::any::{type_name, TypeId};
use core::cell::{Cell, RefCell, UnsafeCell};
use core::hash::{BuildHasher, BuildHasherDefault, Hasher};
use core::num::{NonZeroU128, NonZeroU32};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, null, null_mut, NonNull};
use core::sync::atomic::{AtomicU32, Ordering};
use core::{arch, fmt};
use std::thread::current;

use alloc::alloc::alloc_zeroed;
use bevy_reflect::{Reflect, ReflectFromPtr};
use hashbrown::{hash_map::DefaultHashBuilder, HashMap};

use crate::borrow::AtomicBorrow;
use crate::query::Fetch;
use crate::{world, Access, Component, ComponentRef, Query};

/// A collection of entities having the same component types
///
/// Accessing `Archetype`s is only required in niche cases. Typical use should go through the
/// [`World`](crate::World).
pub struct Archetype {
    types: Vec<TypeInfo>,
    type_ids: Box<[TypeId]>,
    index: OrderedTypeIdMap<usize>,
    len: U32Cell,
    num_free: U32Cell,
    entities: KVec<U32Cell>,
    /// One allocation per type, in the same order as `types`
    data: Box<[Data]>,
    first_free: PtrCell<u8>,
}

impl Archetype {
    fn assert_type_info(types: &[TypeInfo]) {
        types.windows(2).for_each(|x| match x[0].cmp(&x[1]) {
            core::cmp::Ordering::Less => (),
            #[cfg(debug_assertions)]
            core::cmp::Ordering::Equal => panic!(
                "attempted to allocate entity with duplicate {} components; \
                 each type must occur at most once!",
                x[0].type_name
            ),
            #[cfg(not(debug_assertions))]
            core::cmp::Ordering::Equal => panic!(
                "attempted to allocate entity with duplicate components; \
                 each type must occur at most once!"
            ),
            core::cmp::Ordering::Greater => panic!("type info is unsorted"),
        });
    }

    pub(crate) fn new(types: Vec<TypeInfo>) -> Self {
        Self::assert_type_info(&types);
        Self {
            index: OrderedTypeIdMap::new(types.iter().enumerate().map(|(i, ty)| (ty.id, i))),
            type_ids: types.iter().map(|ty| ty.id()).collect(),
            entities: KVec::new(),
            len: U32Cell::new(0),
            num_free: U32Cell::new(0),
            data: types
                .iter()
                .map(|ty| {
                    let header_layout = Layout::new::<StorageHeader>();
                    let len = header_layout.size();
                    // calculate padding needed to align the type.
                    // code taken from Layout::padding_needed_for
                    let len_rounded_up = len.wrapping_add(ty.gc_layout.align()).wrapping_sub(1)
                        & !ty.gc_layout.align().wrapping_sub(1);
                    let padding_to_align = len_rounded_up.wrapping_sub(len);
                    let header_layout = Layout::from_size_align(
                        header_layout.size() + padding_to_align,
                        DATA_CHUNK_SIZE_BYTES,
                    )
                    .unwrap();
                    Data {
                        state: AtomicBorrow::new(),
                        stride: ty.gc_layout().size(),
                        value_start: ty.data_start(),
                        entities_per_chunk: (DATA_CHUNK_SIZE_BYTES - header_layout.size())
                            / ty.gc_layout.size(),
                        storage: KVec::new(),
                        header_layout,
                        data_start: header_layout.size(),
                        storage_layout: Layout::from_size_align(
                            DATA_CHUNK_SIZE_BYTES,
                            DATA_CHUNK_SIZE_BYTES,
                        )
                        .unwrap(),
                    }
                })
                .collect(),
            types,
            first_free: PtrCell::new(null_mut()),
        }
    }

    pub(crate) fn clear(&mut self) {
        // clear component values, mark tombstones and
        for (ty, data) in self.types.iter().zip(&*self.data) {
            // SAFETY: we have &mut self
            for index in 0..unsafe { self.len.read_nonsync() } {
                unsafe {
                    let mut removed = data.get_gc_ptr(index);
                    if matches!(
                        removed.header_ptr().as_ref().state,
                        crate::gc::State::Alive { .. }
                    ) {
                        debug_assert!(
                            removed.header_ptr().as_ref().state
                                == crate::gc::State::Alive {
                                    borrow: core::cell::Cell::new(0)
                                }
                        );
                        removed.drop_value_and_tombstone(ty);
                    }
                }
            }
        }
        self.entities.fill(u32::MAX.into());
    }

    /// Whether this archetype contains `T` components
    pub fn has<T: Component>(&self) -> bool {
        self.has_dynamic(TypeId::of::<T>())
    }

    /// Whether this archetype contains components with the type identified by `id`
    pub fn has_dynamic(&self, id: TypeId) -> bool {
        self.index.contains_key(&id)
    }

    /// Find the state index associated with `T`, if present
    pub(crate) fn get_state<T: Component>(&self) -> Option<usize> {
        self.index.get(&TypeId::of::<T>()).copied()
    }

    // /// Borrow all components of a single type from these entities, if present
    // ///
    // /// `T` must be a shared or unique reference to a component type.
    // ///
    // /// Useful for efficient serialization.
    // pub fn get<'a, T: ComponentRef<'a>>(&'a self) -> Option<T::Column> {
    //     T::get_column(self)
    // }

    pub(crate) fn borrow<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, TypeId::of::<T>());

        if !self.data[state].state.borrow() {
            panic!("{} already borrowed uniquely", type_name::<T>());
        }
    }

    pub(crate) fn borrow_mut<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, TypeId::of::<T>());

        if !self.data[state].state.borrow_mut() {
            panic!("{} already borrowed", type_name::<T>());
        }
    }

    pub(crate) fn release<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, TypeId::of::<T>());
        self.data[state].state.release();
    }

    pub(crate) fn release_mut<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, TypeId::of::<T>());
        self.data[state].state.release_mut();
    }

    #[inline]
    pub(crate) unsafe fn allocated_values_nonsync(&self) -> u32 {
        self.len.read_nonsync()
    }

    #[inline]
    pub(crate) fn allocated_values_sync(&self) -> u32 {
        self.len.load_atomic(Ordering::Relaxed)
    }

    /// Whether this archetype contains no entities
    #[inline]
    pub unsafe fn is_empty_nonsync(&self) -> bool {
        self.len.read_nonsync() - self.num_free.read_nonsync() == 0
    }
    #[inline]
    pub fn is_empty_sync(&self) -> bool {
        self.len.load_atomic(Ordering::Relaxed) - self.num_free.load_atomic(Ordering::Relaxed) == 0
    }

    #[inline]
    pub(crate) fn entities(&self) -> NonNull<u32> {
        unsafe { NonNull::new_unchecked(self.entities.as_ptr() as *mut u32) }
    }

    pub(crate) fn entity_id(&self, index: u32) -> u32 {
        (&self.entities[index as usize]).into()
    }

    #[inline]
    pub(crate) fn set_entity_id(&mut self, index: usize, id: u32) {
        self.entities[index].set(id);
    }

    pub(crate) fn types(&self) -> &[TypeInfo] {
        &self.types
    }

    pub(crate) fn type_ids(&self) -> &[TypeId] {
        &self.type_ids
    }

    /// Enumerate the types of the components of entities stored in this archetype.
    ///
    /// Convenient for dispatching logic which needs to be performed on sets of type ids.  For
    /// example, suppose you're building a scripting system, and you want to integrate the scripting
    /// language with your ECS. This functionality allows you to iterate through all of the
    /// archetypes of the world with [`World::archetypes()`](crate::World::archetypes()) and extract
    /// all possible combinations of component types which are currently stored in the `World`.
    /// From there, you can then create a mapping of archetypes to wrapper objects for your
    /// scripting language that provide functionality based off of the components of any given
    /// [`Entity`], and bind them onto an [`Entity`] when passed into your scripting language by
    /// looking up the [`Entity`]'s archetype using
    /// [`EntityRef::component_types`](crate::EntityRef::component_types).
    ///
    /// [`Entity`]: crate::Entity
    pub fn component_types(&self) -> impl ExactSizeIterator<Item = TypeId> + '_ {
        self.types.iter().map(|typeinfo| typeinfo.id)
    }

    /// `index` must be in-bounds or just past the end
    pub(crate) unsafe fn get_data_storage(&self, state: usize) -> &Data {
        debug_assert!(state < self.types.len());
        self.data.get_unchecked(state)
    }
    pub(crate) unsafe fn get_data_storage_mut(&mut self, state: usize) -> NonNull<Data> {
        debug_assert!(state < self.types.len());
        NonNull::new_unchecked(self.data.as_mut_ptr().add(state))
    }

    pub(crate) unsafe fn get_dynamic(&self, ty: &TypeInfo, index: u32) -> Option<GCPtr> {
        debug_assert!(index < self.len.read_nonsync());
        debug_assert!(self.entities[index as usize].read_nonsync() != u32::MAX);
        let ptr = self
            .data
            .get_unchecked(*self.index.get(&ty.id())?)
            .get_gc_ptr(index);

        Some(ptr)
    }

    /// Every type must be written immediately after this call
    /// This cannot be called from multiple threads concurrently
    pub(crate) unsafe fn allocate_nonsync(&self, id: u32, world_slot: NonZeroU32) -> u32 {
        let free_ptr = self.first_free.read_nonsync();
        let new_slot =
            if let Some(free_value) = NonNull::new(free_ptr).map(|ptr| GCPtr { value: ptr }) {
                let gc_header = unsafe { &mut *free_value.header_ptr().as_ptr() };
                let crate::gc::State::Free { next_free } = gc_header.state else {
                    panic!("value in free list but state is not free")
                };
                gc_header.state = crate::gc::State::Free { next_free: None };
                self.first_free.write_nonsync(
                    next_free
                        .map(|ptr| ptr.value.as_ptr())
                        .unwrap_or(null_mut()),
                );
                let current_num_free = self.num_free.read_nonsync();
                self.num_free.write_nonsync(current_num_free - 1);
                let new_slot = free_value.archetype_slot();
                new_slot
            } else {
                let new_slot = self.len.read_nonsync();
                self.len.write_nonsync(new_slot + 1);
                if new_slot as usize >= self.entities.len_nonsync() {
                    self.grow_nonsync(64, world_slot);
                }
                new_slot
            };
        self.entities[new_slot as usize].write_nonsync(id);
        new_slot
    }

    // pub(crate) unsafe fn set_len(&mut self, len: u32) {
    //     debug_assert!(len <= self.capacity());
    //     self.len.store(len);
    // }

    pub(crate) fn reserve(&mut self, additional: u32, world_slot: NonZeroU32) {
        if additional > (self.capacity() - self.len.read()) {
            let increment = additional - (self.capacity() - self.len.read());
            self.grow(increment.max(64), world_slot);
        }
    }

    pub(crate) fn capacity(&self) -> u32 {
        self.entities.len() as u32
    }

    /// Increase capacity by at least `min_increment`
    fn grow_sync(&self, min_increment: u32, world_slot: NonZeroU32) {
        // Double capacity or increase it by `min_increment`, whichever is larger.
        let additional = self.capacity().max(min_increment) as usize;
        let new_cap = self.entities.len() + additional;
        self.entities.extend_with_sync(additional, u32::MAX.into());

        for (info, data) in self.types.iter().zip(&*self.data) {
            if info.value_layout.size() != 0 {
                let entities_per_chunk = data.entities_per_chunk;
                let num_chunks_required = new_cap / entities_per_chunk + 1;
                let new_chunks = num_chunks_required.saturating_sub(data.storage.len());
                for _ in 0..new_chunks {
                    unsafe {
                        let mem = alloc_zeroed(data.storage_layout);
                        assert!(!mem.is_null(), "allocation failed");
                        mem.cast::<StorageHeader>()
                            .write(data.new_storage_header(world_slot, data.storage.len()));
                        data.storage.push_sync(mem);
                    }
                }
            }
        }
    }

    /// Increase capacity by at least `min_increment`
    unsafe fn grow_nonsync(&self, min_increment: u32, world_slot: NonZeroU32) {
        // Double capacity or increase it by `min_increment`, whichever is larger.
        let additional = self.capacity().max(min_increment) as usize;
        let new_cap = self.entities.len() + additional;
        self.entities
            .extend_with_nonsync(additional, u32::MAX.into());

        for (info, data) in self.types.iter().zip(&*self.data) {
            if info.value_layout.size() != 0 {
                let entities_per_chunk =
                    (DATA_CHUNK_SIZE_BYTES - data.data_start) / info.gc_layout.size();
                let num_chunks_required = new_cap / entities_per_chunk + 1;
                let new_chunks = num_chunks_required.saturating_sub(data.storage.len());
                for _ in 0..new_chunks {
                    unsafe {
                        let mem = alloc_zeroed(data.storage_layout);
                        assert!(!mem.is_null(), "allocation failed");
                        mem.cast::<StorageHeader>()
                            .write(data.new_storage_header(world_slot, data.storage.len()));
                        data.storage.push_nonsync(mem);
                    }
                }
            }
        }
    }

    /// Increase capacity by at least `min_increment`
    fn grow(&mut self, min_increment: u32, world_slot: NonZeroU32) {
        // Double capacity or increase it by `min_increment`, whichever is larger.
        let additional = self.capacity().max(min_increment) as usize;
        let new_cap = self.entities.len() + additional;
        self.entities.extend_with(additional, u32::MAX.into());

        for (info, data) in self.types.iter().zip(self.data.iter_mut()) {
            if info.value_layout.size() != 0 {
                let entities_per_chunk =
                    (DATA_CHUNK_SIZE_BYTES - data.data_start) / info.gc_layout.size();
                let num_chunks_required = new_cap / entities_per_chunk + 1;
                let new_chunks = num_chunks_required.saturating_sub(data.storage.len());
                for _ in 0..new_chunks {
                    unsafe {
                        let mem = alloc_zeroed(data.storage_layout);
                        assert!(!mem.is_null(), "allocation failed");
                        mem.cast::<StorageHeader>()
                            .write(data.new_storage_header(world_slot, data.storage.len()));
                        data.storage.push(mem);
                    }
                }
            }
        }
    }

    pub(crate) unsafe fn remove(&mut self, index: u32) {
        for (ty, data) in self.types.iter().zip(&*self.data) {
            let mut to_remove = data.get_gc_ptr(index);
            to_remove.drop_value_and_tombstone(ty);
        }
        self.entities[index as usize].set(u32::MAX);
    }

    /// Returns the ID of the entity moved into `index`, if any
    pub(crate) unsafe fn move_to(
        &mut self,
        index: u32,
        mut f: impl FnMut(GCPtr, &TypeInfo),
    ) -> Option<u32> {
        for (ty, data) in self.types.iter().zip(&*self.data) {
            let gc_ptr = data.get_gc_ptr(index);
            f(gc_ptr, ty);
            self.entities[index as usize].set(u32::MAX);
        }
        None
    }

    pub(crate) unsafe fn put_new_dynamic_nonsync(
        &self,
        component_data: *mut u8,
        ty: &TypeInfo,
        index: u32,
    ) {
        let mut ptr = self.get_dynamic(ty, index).unwrap();
        ptr.move_from_value(ty, component_data);
    }

    pub(crate) unsafe fn move_from_nonsync(&self, gc_ptr: GCPtr, ty: &TypeInfo, index: u32) {
        let mut ptr = self.get_dynamic(ty, index).unwrap();
        ptr.move_from(ty, gc_ptr);
    }

    /// How, if at all, `Q` will access entities in this archetype
    pub fn access<Q: Query>(&self) -> Option<Access> {
        Q::Fetch::access(self)
    }

    /// Add components from another archetype with identical components
    ///
    /// # Safety
    ///
    /// Component types must match exactly.
    pub(crate) unsafe fn merge(&mut self, mut other: Archetype, world_slot: NonZeroU32) {
        self.reserve(other.len.read(), world_slot);
        for ((info, dst), src) in self.types.iter().zip(&*self.data).zip(&*other.data) {
            todo!();
            // dst.storage
            //     .as_ptr()
            //     .add(self.len as usize * info.gc_layout.size())
            //     .copy_from_nonoverlapping(
            //         src.storage.as_ptr(),
            //         other.len as usize * info.gc_layout.size(),
            //     )
        }
        let len = self.len.read();
        self.len.set(len + other.len.read());
        other.len.set(0);
    }

    pub(crate) unsafe fn free_slot(&self, slot: u32) {
        let current_num_free = self.num_free.read_nonsync();
        self.num_free.write_nonsync(current_num_free + 1);
        debug_assert!(
            self.len.read_nonsync() >= current_num_free + 1,
            "allocated len is {} and num free is {}",
            self.len.read_nonsync(),
            current_num_free + 1
        );

        let current_free_head = self.first_free.read_nonsync();
        let mut new_free_head = None;
        for (idx, storage) in self.data.iter().enumerate() {
            let slot_ptr = storage.get_gc_ptr(slot);
            if idx == 0 {
                slot_ptr.header_ptr().as_mut().state = crate::gc::State::Free {
                    next_free: NonNull::new(current_free_head).map(|ptr| GCPtr { value: ptr }),
                };
                new_free_head = Some(slot_ptr);
            } else {
                slot_ptr.header_ptr().as_mut().state = crate::gc::State::Free { next_free: None };
            }
        }
        self.first_free.write_nonsync(
            new_free_head
                .map(|ptr| ptr.value.as_ptr())
                .unwrap_or(null_mut()),
        );
    }

    // /// Raw IDs of the entities in this archetype
    // ///
    // /// Convertible into [`Entity`](crate::Entity)s with
    // /// [`World::find_entity_from_id()`](crate::World::find_entity_from_id). Useful for efficient
    // /// serialization.
    // #[inline]
    // pub unsafe fn ids(&self) -> &[u32] {
    //     &self.entities[0..self.len() as usize]
    // }
}

impl Drop for Archetype {
    fn drop(&mut self) {
        if self.entities.len() == 0 {
            return;
        }
        for (info, data) in self.types.iter().zip(&*self.data) {
            let mut needs_leak = false;
            for index in 0..self.len.read() {
                unsafe {
                    let ptr = data.get_gc_ptr(index);
                    let is_free = matches!(
                        ptr.header_ptr().as_ref().state,
                        crate::gc::State::Free { .. }
                    );
                    #[cfg(debug_assertions)]
                    if !is_free {
                        if !std::thread::panicking() {
                            std::eprintln!(
                                "Archetype storage dropped without freeing dead values: {:?} at id {} was state {:?}",
                                info, index, ptr.header_ptr().as_ref().state
                            );
                        }
                    }
                    needs_leak |= !is_free;
                }
            }
            if info.value_layout.size() != 0 && !needs_leak {
                for chunk in data.chunks() {
                    assert!(!chunk.is_null());
                    unsafe {
                        dealloc(
                            *chunk,
                            Layout::from_size_align_unchecked(
                                DATA_CHUNK_SIZE_BYTES,
                                DATA_CHUNK_SIZE_BYTES,
                            ),
                        );
                    }
                }
            }
        }
        self.data = Box::default();
    }
}

pub(crate) const DATA_CHUNK_SIZE_BYTES: usize = 0x10000;
pub(crate) struct StorageHeader {
    pub(crate) world_slot: NonZeroU32,
    pub(crate) chunk_idx: usize,
    pub(crate) data_start: usize,
    pub(crate) stride: usize,
}
pub(crate) struct Data {
    storage: KVec<*mut u8>,
    storage_layout: Layout,
    header_layout: Layout,
    state: AtomicBorrow,
    stride: usize,
    value_start: usize,
    data_start: usize,
    entities_per_chunk: usize,
}

impl Data {
    pub(crate) fn new_storage_header(
        &self,
        world_slot: NonZeroU32,
        chunk_idx: usize,
    ) -> StorageHeader {
        StorageHeader {
            world_slot,
            chunk_idx,
            data_start: self.data_start,
            stride: self.stride,
        }
    }
    #[inline(always)]
    pub(crate) fn chunks(&self) -> &[*mut u8] {
        &self.storage
    }
    #[inline(always)]
    pub(crate) fn stride(&self) -> usize {
        self.stride
    }
    #[inline(always)]
    pub(crate) fn value_start(&self) -> usize {
        self.value_start
    }
    #[inline(always)]
    pub(crate) fn data_start(&self) -> usize {
        self.data_start
    }
    #[inline(always)]
    pub(crate) fn entities_per_chunk(&self) -> usize {
        self.entities_per_chunk
    }

    pub(crate) unsafe fn get_gc_ptr(&self, idx: u32) -> GCPtr {
        let idx = idx as usize;
        let entities_per_chunk = self.entities_per_chunk;
        let chunk_idx = idx / entities_per_chunk;
        let value_idx = idx % entities_per_chunk;
        GCPtr::from_base_with_offset(
            self.value_start,
            NonNull::new_unchecked(
                self.storage
                    .get_unchecked(chunk_idx)
                    .add(self.data_start + value_idx * self.stride),
            ),
        )
    }

    pub(crate) unsafe fn get_value(&self, idx: u32) -> NonNull<u8> {
        let idx = idx as usize;
        let entities_per_chunk = self.entities_per_chunk;
        let chunk_idx = idx / entities_per_chunk;
        let value_idx = idx % entities_per_chunk;
        unsafe {
            NonNull::new_unchecked(
                self.storage
                    .get_unchecked(chunk_idx)
                    .add(self.data_start + value_idx * self.stride + self.value_start),
            )
        }
    }

    pub(crate) unsafe fn iter_gc_ptr<'a>(
        &'a self,
        num_allocated_slots: u32,
    ) -> impl IntoIterator<Item = GCPtr> + 'a {
        DataGCPtrIterator {
            storage: self,
            entities_per_chunk: self.entities_per_chunk,
            data_start: self.data_start,
            value_start: self.value_start,
            stride: self.stride,
            num_allocated_slots,
            chunk_idx: 0,
            slot_idx: 0,
            value_idx: 0,
            curr_chunk: self.chunks().get(0).copied().unwrap_or(null_mut()),
        }
    }
}

struct DataGCPtrIterator<'a> {
    storage: &'a Data,
    entities_per_chunk: usize,
    data_start: usize,
    value_start: usize,
    stride: usize,
    num_allocated_slots: u32,
    // stateful variables
    chunk_idx: usize,
    slot_idx: u32,
    value_idx: usize,
    curr_chunk: *mut u8,
}
impl<'a> Iterator for DataGCPtrIterator<'a> {
    type Item = GCPtr;

    fn next(&mut self) -> Option<Self::Item> {
        if self.slot_idx >= self.num_allocated_slots {
            return None;
        }
        assert!(!self.curr_chunk.is_null());
        if self.value_idx >= self.entities_per_chunk {
            self.chunk_idx += 1;
            self.curr_chunk = self.storage.chunks()[self.chunk_idx];
            self.value_idx = 0;
        }
        let ptr = unsafe {
            GCPtr::from_base_with_offset(
                self.value_start,
                NonNull::new_unchecked(
                    self.curr_chunk
                        .add(self.data_start + self.stride * self.value_idx),
                ),
            )
        };
        self.value_idx += 1;
        self.slot_idx += 1;
        Some(ptr)
    }
}

/// A hasher optimized for hashing a single TypeId.
///
/// TypeId is already thoroughly hashed, so there's no reason to hash it again.
/// Just leave the bits unchanged.
#[derive(Default)]
pub(crate) struct TypeIdHasher {
    hash: u64,
}

impl Hasher for TypeIdHasher {
    fn write_u64(&mut self, n: u64) {
        // Only a single value can be hashed, so the old hash should be zero.
        debug_assert_eq!(self.hash, 0);
        self.hash = n;
    }

    // Tolerate TypeId being either u64 or u128.
    fn write_u128(&mut self, n: u128) {
        debug_assert_eq!(self.hash, 0);
        self.hash = n as u64;
    }

    fn write(&mut self, bytes: &[u8]) {
        debug_assert_eq!(self.hash, 0);

        // This will only be called if TypeId is neither u64 nor u128, which is not anticipated.
        // In that case we'll just fall back to using a different hash implementation.
        let mut hasher = <DefaultHashBuilder as BuildHasher>::Hasher::default();
        hasher.write(bytes);
        self.hash = hasher.finish();
    }

    fn finish(&self) -> u64 {
        self.hash
    }
}

/// A HashMap with TypeId keys
///
/// Because TypeId is already a fully-hashed u64 (including data in the high seven bits,
/// which hashbrown needs), there is no need to hash it again. Instead, this uses the much
/// faster no-op hash.
pub(crate) type TypeIdMap<V> = HashMap<TypeId, V, BuildHasherDefault<TypeIdHasher>>;

struct OrderedTypeIdMap<V>(Box<[(TypeId, V)]>);

impl<V> OrderedTypeIdMap<V> {
    fn new(iter: impl Iterator<Item = (TypeId, V)>) -> Self {
        let mut vals = iter.collect::<Box<[_]>>();
        vals.sort_unstable_by_key(|(id, _)| *id);
        Self(vals)
    }

    fn search(&self, id: &TypeId) -> Option<usize> {
        self.0.binary_search_by_key(id, |(id, _)| *id).ok()
    }

    fn contains_key(&self, id: &TypeId) -> bool {
        self.search(id).is_some()
    }

    fn get(&self, id: &TypeId) -> Option<&V> {
        self.search(id).map(move |idx| &self.0[idx].1)
    }
}

/// Metadata required to store a component.
///
/// All told, this means a [`TypeId`], to be able to dynamically name/check the component type; a
/// [`Layout`], so that we know how to allocate memory for this component type; and a drop function
/// which internally calls [`core::ptr::drop_in_place`] with the correct type parameter.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    id: TypeId,
    value_layout: Layout,
    gc_layout: Layout,
    drop: unsafe fn(*mut u8),
    reflect_from_ptr: unsafe fn(*mut u8) -> *mut dyn Reflect,
    data_start: usize,
    #[cfg(debug_assertions)]
    type_name: &'static str,
}

impl TypeInfo {
    /// Construct a `TypeInfo` directly from the static type.
    pub fn of<T: Reflect + 'static>() -> Self {
        unsafe fn drop_ptr<T>(x: *mut u8) {
            x.cast::<T>().drop_in_place()
        }

        let type_layout = Layout::new::<T>();
        let (gc_layout, data_start) = Layout::new::<GCHeader>().extend(type_layout).unwrap();
        let gc_layout = gc_layout.pad_to_align();
        assert!(gc_layout.size() == Layout::new::<GC<T>>().size());

        Self {
            id: TypeId::of::<T>(),
            gc_layout,
            value_layout: type_layout,
            data_start,
            drop: drop_ptr::<T>,
            reflect_from_ptr: |ptr| unsafe { &mut *ptr.cast::<T>() as &mut dyn Reflect },
            #[cfg(debug_assertions)]
            type_name: core::any::type_name::<T>(),
        }
    }

    /// Construct a `TypeInfo` from its components. This is useful in the rare case that you have
    /// some kind of pointer to raw bytes/erased memory holding a component type, coming from a
    /// source unrelated to hecs, and you want to treat it as an insertable component by
    /// implementing the `DynamicBundle` API.
    pub fn from_parts(
        id: TypeId,
        layout: Layout,
        drop: unsafe fn(*mut u8),
        reflect_from_ptr: unsafe fn(*mut u8) -> *mut dyn Reflect,
    ) -> Self {
        let (gc_layout, data_start) = Layout::new::<GCHeader>().extend(layout).unwrap();
        let gc_layout = gc_layout.pad_to_align();

        Self {
            id,
            gc_layout,
            value_layout: layout,
            data_start,
            reflect_from_ptr,
            drop,
            #[cfg(debug_assertions)]
            type_name: "<unknown> (TypeInfo constructed from parts)",
        }
    }

    /// Access the `TypeId` for this component type.
    pub fn id(&self) -> TypeId {
        self.id
    }

    /// Access the `Layout` of this component type as if it were wrapped with a GC<T>.
    pub fn gc_layout(&self) -> Layout {
        self.gc_layout
    }

    /// Access the `Layout` of this component type.
    pub fn value_layout(&self) -> Layout {
        self.value_layout
    }

    /// The byte offset of the gc_layout where value_layout starts.
    pub fn data_start(&self) -> usize {
        self.data_start
    }

    /// Directly call the destructor on a pointer to data of this component type.
    ///
    /// # Safety
    ///
    /// All of the caveats of [`core::ptr::drop_in_place`] apply, with the additional requirement
    /// that this method is being called on a pointer to an object of the correct component type.
    pub unsafe fn drop_value(&self, data: *mut u8) {
        (self.drop)(data);
    }

    pub fn reflect_from_ptr(&self) -> unsafe fn(*mut u8) -> *mut dyn Reflect {
        self.reflect_from_ptr
    }

    /// Get the function pointer encoding the destructor for the component type this `TypeInfo`
    /// represents.
    pub fn drop_shim(&self) -> unsafe fn(*mut u8) {
        self.drop
    }
}

impl PartialOrd for TypeInfo {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypeInfo {
    /// Order by alignment, descending. Ties broken with TypeId.
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.gc_layout
            .align()
            .cmp(&other.gc_layout.align())
            .reverse()
            .then_with(|| self.id.cmp(&other.id))
    }
}

impl PartialEq for TypeInfo {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for TypeInfo {}

// / Shared reference to a single column of component data in an [`Archetype`]
// pub struct ArchetypeColumn<'a, T: Component> {
//     archetype: &'a Archetype,
//     column: &'a [GC<T>],
// }

// impl<'a, T: Component> ArchetypeColumn<'a, T> {
//     pub(crate) fn new(archetype: &'a Archetype) -> Option<Self> {
//         let state = archetype.get_state::<T>()?;
//         let ptr = archetype.get_base::<T>(state);
//         let column = unsafe { core::slice::from_raw_parts(ptr.as_ptr(), archetype.len() as usize) };
//         archetype.borrow::<T>(state);
//         Some(Self { archetype, column })
//     }
// }

// impl<T: Component> Deref for ArchetypeColumn<'_, T> {
//     type Target = [GC<T>];
//     fn deref(&self) -> &[GC<T>] {
//         self.column
//     }
// }

// impl<T: Component> Drop for ArchetypeColumn<'_, T> {
//     fn drop(&mut self) {
//         let state = self.archetype.get_state::<T>().unwrap();
//         self.archetype.release::<T>(state);
//     }
// }

// impl<T: Component> Clone for ArchetypeColumn<'_, T> {
//     fn clone(&self) -> Self {
//         let state = self.archetype.get_state::<T>().unwrap();
//         self.archetype.borrow::<T>(state);
//         Self {
//             archetype: self.archetype,
//             column: self.column,
//         }
//     }
// }

// impl<T: Component + fmt::Debug> fmt::Debug for ArchetypeColumn<'_, T> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.column.fmt(f)
//     }
// }

// /// Unique reference to a single column of component data in an [`Archetype`]
// pub struct ArchetypeColumnMut<'a, T: Component> {
//     archetype: &'a Archetype,
//     column: &'a mut [GC<T>],
// }

// impl<'a, T: Component> ArchetypeColumnMut<'a, T> {
//     pub(crate) fn new(archetype: &'a Archetype) -> Option<Self> {
//         let state = archetype.get_state::<T>()?;
//         let ptr = archetype.get_base::<T>(state);
//         let column =
//             unsafe { core::slice::from_raw_parts_mut(ptr.as_ptr(), archetype.len() as usize) };
//         archetype.borrow_mut::<T>(state);
//         Some(Self { archetype, column })
//     }
// }

// impl<T: Component> Deref for ArchetypeColumnMut<'_, T> {
//     type Target = [GC<T>];
//     fn deref(&self) -> &[GC<T>] {
//         self.column
//     }
// }

// impl<T: Component> DerefMut for ArchetypeColumnMut<'_, T> {
//     fn deref_mut(&mut self) -> &mut [GC<T>] {
//         self.column
//     }
// }

// impl<T: Component> Drop for ArchetypeColumnMut<'_, T> {
//     fn drop(&mut self) {
//         let state = self.archetype.get_state::<T>().unwrap();
//         self.archetype.release_mut::<T>(state);
//     }
// }

// impl<T: Component + fmt::Debug> fmt::Debug for ArchetypeColumnMut<'_, T> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.column.fmt(f)
//     }
// }
