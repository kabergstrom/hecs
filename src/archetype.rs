// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::alloc::alloc::{alloc, dealloc, Layout};
use crate::alloc::boxed::Box;
use crate::alloc::{vec, vec::Vec};
use crate::gc::cells::{EntityCell, PtrCell, U32Cell};
use crate::gc::kvec::KVec;
use crate::gc::header::{self as gch, Geometry, HeaderWord, CHUNK_BYTES, HEADERS_OFFSET, HEADER_BYTES};
use crate::gc::GCPtr;
use core::any::type_name;

use crate::{Entity, StableTypeId};
use core::cell::{Cell, RefCell, UnsafeCell};
use core::hash::{BuildHasher, BuildHasherDefault, Hasher};
use core::num::{NonZeroU128, NonZeroU32};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, null, null_mut, NonNull};
use core::sync::atomic::{AtomicU32, Ordering};
use core::{arch, fmt};
use std::thread::current;

use alloc::alloc::alloc_zeroed;
use hashbrown::{hash_map::DefaultHashBuilder, HashMap};
#[cfg(feature = "mirror_mirror")]
use mirror_mirror::Reflect;

use crate::borrow::AtomicBorrow;
use crate::query::Fetch;
use crate::{world, Access, Component, ComponentRef, Query};

/// A collection of entities having the same component types
///
/// Accessing `Archetype`s is only required in niche cases. Typical use should go through the
/// [`World`](crate::World).
pub struct Archetype {
    types: Vec<TypeInfo>,
    type_ids: Box<[StableTypeId]>,
    index: OrderedTypeIdMap<usize>,
    len: U32Cell,
    num_free: U32Cell,
    entities: KVec<EntityCell>,
    /// One allocation per type, in the same order as `types`
    data: Box<[Data]>,
    /// Free rows, a stack: `free_slot` pushes, `allocate_nonsync` pops (last freed, first
    /// reused). A side structure rather than a link in the free cells, so a free cell's value
    /// bytes stay untouched and any value size (zero-sized included) works.
    free_rows: FreeRows,
    /// Per row, how many times the sweep has freed it ([`row_generation`](Self::row_generation)).
    row_gens: RowGens,
}

/// Per-row free counts, grown on demand (a row never freed reads 0).
#[derive(Default)]
struct RowGens(UnsafeCell<Vec<u32>>);
// SAFETY: `get` and `bump` are `unsafe` with NS contracts (a `bump` may reallocate); `clear`
// takes `&mut self`. Cross-thread sharing of the owning `Archetype` relies on the engine's
// single-thread invariant (see the `Send` impl of `gc::GCPtr`).
unsafe impl Sync for RowGens {}

impl RowGens {
    /// # Safety
    /// No concurrent [`bump`](Self::bump) (it may reallocate).
    unsafe fn get(&self, slot: u32) -> u32 {
        (&*self.0.get()).get(slot as usize).copied().unwrap_or(0)
    }

    /// Count one more free of `slot`, wrapping below `u32::MAX` (which callers may keep as a
    /// "matches no generation" sentinel).
    ///
    /// # Safety
    /// NS: no concurrent `get` or `bump`.
    unsafe fn bump(&self, slot: u32) {
        let gens = &mut *self.0.get();
        if slot as usize >= gens.len() {
            gens.resize(slot as usize + 1, 0);
        }
        let g = &mut gens[slot as usize];
        *g = if *g >= u32::MAX - 1 { 0 } else { *g + 1 };
    }

    fn clear(&mut self) {
        self.0.get_mut().clear();
    }
}

/// The archetype's free rows (see `Archetype::free_rows`).
#[derive(Default)]
struct FreeRows(UnsafeCell<Vec<u32>>);
// SAFETY: as `RowGens`: every access is an NS `unsafe` method.
unsafe impl Sync for FreeRows {}

impl FreeRows {
    /// # Safety
    /// NS.
    unsafe fn push(&self, row: u32) {
        (*self.0.get()).push(row);
    }

    /// # Safety
    /// NS.
    unsafe fn pop(&self) -> Option<u32> {
        (*self.0.get()).pop()
    }
}

/// What a row holding no entity holds ([`Archetype::vacancy`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vacancy {
    /// Every column `Dead` or `Moved`: a tombstone, kept until a sweep finds it unreferenced.
    Tombstone,
    /// Every column `Free`: on the free list; nothing references it.
    Free,
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
                    let geometry = ty.geometry();
                    Data {
                        state: AtomicBorrow::new(),
                        stride: geometry.stride,
                        values_start: geometry.values_start,
                        entities_per_chunk: geometry.capacity,
                        recip: geometry.recip(),
                        storage: KVec::new(),
                        storage_layout: Layout::from_size_align(
                            DATA_CHUNK_SIZE_BYTES,
                            DATA_CHUNK_SIZE_BYTES,
                        )
                        .unwrap(),
                    }
                })
                .collect(),
            types,
            free_rows: FreeRows::default(),
            row_gens: RowGens::default(),
        }
    }

    pub(crate) fn clear(&mut self) {
        // clear component values, mark tombstones and
        for (ty, data) in self.types.iter().zip(&*self.data) {
            // SAFETY: we have &mut self
            for index in 0..unsafe { self.len.read_nonsync() } {
                unsafe {
                    let w = data.header(index).get();
                    if gch::state(w) == gch::ALIVE {
                        debug_assert!(gch::is_movable(w), "clearing a borrowed component");
                        data.get_gc_ptr(index).drop_value_and_tombstone(ty);
                    }
                }
            }
        }
        self.entities.fill(EntityCell::free());
        self.row_gens.clear();
    }

    /// Whether this archetype contains `T` components
    pub fn has<T: Component>(&self) -> bool {
        self.has_dynamic(T::STABLE_TYPE_ID)
    }

    /// Whether this archetype contains components with the type identified by `id`
    pub fn has_dynamic(&self, id: StableTypeId) -> bool {
        self.index.contains_key(&id)
    }

    /// Find the state index associated with `T`, if present
    pub(crate) fn get_state<T: Component>(&self) -> Option<usize> {
        self.index.get(&T::STABLE_TYPE_ID).copied()
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
        assert_eq!(self.types[state].id, T::STABLE_TYPE_ID);

        if !self.data[state].state.borrow() {
            panic!("{} already borrowed uniquely", type_name::<T>());
        }
    }

    pub(crate) fn borrow_mut<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, T::STABLE_TYPE_ID);

        if !self.data[state].state.borrow_mut() {
            panic!("{} already borrowed", type_name::<T>());
        }
    }

    pub(crate) fn release<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, T::STABLE_TYPE_ID);
        self.data[state].state.release();
    }

    pub(crate) fn release_mut<T: Component>(&self, state: usize) {
        assert_eq!(self.types[state].id, T::STABLE_TYPE_ID);
        self.data[state].state.release_mut();
    }

    #[inline]
    /// Slots ever allocated (occupied, free-listed or tombstoned).
    ///
    /// # Safety
    /// NS: no concurrent writer of this archetype.
    pub(crate) unsafe fn allocated_values_nonsync(&self) -> u32 {
        self.len.read_nonsync()
    }

    #[inline]
    pub fn allocated_values_sync(&self) -> u32 {
        self.len.load_atomic(Ordering::Relaxed)
    }

    /// Whether this archetype contains no entities
    #[inline]
    ///
    /// # Safety
    /// NS: no concurrent writer of this archetype.
    pub unsafe fn is_empty_nonsync(&self) -> bool {
        self.len.read_nonsync() - self.num_free.read_nonsync() == 0
    }
    #[inline]
    pub fn is_empty_sync(&self) -> bool {
        self.len.load_atomic(Ordering::Relaxed) - self.num_free.load_atomic(Ordering::Relaxed) == 0
    }

    #[inline]
    pub(crate) fn entities(&self) -> NonNull<EntityCell> {
        unsafe { NonNull::new_unchecked(self.entities.as_ptr() as *mut EntityCell) }
    }

    /// Returns the [`Entity`] occupying `index`. The id field is `u32::MAX`
    /// when the slot is free.
    pub fn entity(&self, index: u32) -> Entity {
        self.entities[index as usize].load_atomic(Ordering::Relaxed)
    }

    pub fn entities_slice(&self) -> &[EntityCell] {
        &self.entities
    }

    #[inline]
    pub(crate) fn set_entity(&mut self, index: usize, entity: Entity) {
        self.entities[index].set(entity);
    }
    #[inline]
    /// # Safety
    /// NS; `index` is below the capacity; no `&EntityCell` read concurrently.
    pub(crate) unsafe fn set_entity_nonsync(&self, index: usize, entity: Entity) {
        self.entities[index].write_nonsync(entity);
    }
    #[inline]
    pub(crate) fn set_entity_free(&mut self, index: usize) {
        self.entities[index].set_free();
    }
    #[inline]
    /// # Safety
    /// As [`set_entity_nonsync`](Self::set_entity_nonsync).
    pub(crate) unsafe fn set_entity_free_nonsync(&self, index: usize) {
        self.entities[index].write_free_nonsync();
    }

    pub fn types(&self) -> &[TypeInfo] {
        &self.types
    }

    pub(crate) fn type_ids(&self) -> &[StableTypeId] {
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
    pub fn component_types(&self) -> impl ExactSizeIterator<Item = StableTypeId> + '_ {
        self.types.iter().map(|typeinfo| typeinfo.id)
    }

    /// The column storage of column `state`.
    ///
    /// # Safety
    /// `state < types().len()`.
    pub unsafe fn get_data_storage(&self, state: usize) -> &Data {
        debug_assert!(state < self.types.len());
        self.data.get_unchecked(state)
    }
    /// # Safety
    /// `state < types().len()`.
    pub(crate) unsafe fn get_data_storage_mut(&mut self, state: usize) -> NonNull<Data> {
        debug_assert!(state < self.types.len());
        NonNull::new_unchecked(self.data.as_mut_ptr().add(state))
    }

    /// The [`GCPtr`] of `ty`'s column at `index`, or `None` if this archetype lacks it.
    ///
    /// # Safety
    /// As [`get_dynamic_by_id`](Self::get_dynamic_by_id).
    pub(crate) unsafe fn get_dynamic(&self, ty: &TypeInfo, index: u32) -> Option<GCPtr> {
        self.get_dynamic_by_id(ty.id(), index)
    }

    /// Resolve the column index for a `StableTypeId`, or `None` if absent.
    pub fn column_index(&self, id: StableTypeId) -> Option<usize> {
        self.index.get(&id).copied()
    }

    /// Get a GC pointer by pre-resolved column index and entity slot.
    ///
    /// # Safety
    /// `col < types().len()` and `index` is below the allocated slots (its chunk exists).
    /// Dereferencing the result later needs STRUCT (or NS with no move since), a borrow of the
    /// slot (a gc guard or a column borrow) and the column's matching type.
    pub unsafe fn get_gc_ptr_by_column(&self, col: usize, index: u32) -> GCPtr {
        unsafe { self.data.get_unchecked(col).get_gc_ptr(index) }
    }

    /// Look up a component's GC pointer by `StableTypeId` and entity index.
    ///
    /// # Safety
    /// `index` is below the allocated slots and the row is occupied (debug-checked); no
    /// concurrent NS writer. Dereferencing the result needs what
    /// [`get_gc_ptr_by_column`](Self::get_gc_ptr_by_column)'s result needs.
    pub unsafe fn get_dynamic_by_id(&self, id: StableTypeId, index: u32) -> Option<GCPtr> {
        debug_assert!(index < self.len.read_nonsync());
        debug_assert!(self.entities[index as usize].read_id_nonsync() != u32::MAX);
        let ptr = self
            .data
            .get_unchecked(*self.index.get(&id)?)
            .get_gc_ptr(index);

        Some(ptr)
    }

    /// Whether every component of row `index`, except those whose id `skip` accepts, is
    /// movable ([`GCPtr::is_movable`]): `Alive`, not pending dead, no gc borrow guard.
    ///
    /// # Safety
    /// NS; `index` is below the allocated slots.
    pub(crate) unsafe fn row_movable(
        &self,
        index: u32,
        skip: impl Fn(StableTypeId) -> bool,
    ) -> bool {
        self.types
            .iter()
            .zip(&*self.data)
            .all(|(ty, data)| skip(ty.id()) || data.get_gc_ptr(index).is_movable())
    }

    /// Every type must be written immediately after this call
    /// This cannot be called from multiple threads concurrently
    ///
    /// # Safety
    /// NS. Every column of the returned row must be written (`move_from_value`/`move_from`)
    /// before anything reads it. A growth adds chunks and grows the entity column (outstanding
    /// slices stay valid but stale).
    pub(crate) unsafe fn allocate_nonsync(&self, entity: Entity, world_slot: NonZeroU32) -> u32 {
        let new_slot = if let Some(free_slot) = self.free_rows.pop() {
                debug_assert!(self
                    .data
                    .iter()
                    .all(|data| gch::state(data.header(free_slot).get()) == gch::FREE));
                let current_num_free = self.num_free.read_nonsync();
                self.num_free.write_nonsync(current_num_free - 1);
                free_slot
            } else {
                let new_slot = self.len.read_nonsync();
                self.len.write_nonsync(new_slot + 1);
                if new_slot as usize >= self.entities.len_nonsync() {
                    self.grow_nonsync(64, world_slot);
                }
                new_slot
            };
        self.entities[new_slot as usize].write_nonsync(entity);
        new_slot
    }

    /// [`allocate_nonsync`](Self::allocate_nonsync) past every allocated row, leaving the free
    /// list alone: a row no copy of slot memory has seen. Its columns are `Free`.
    ///
    /// # Safety
    /// As [`allocate_nonsync`](Self::allocate_nonsync).
    pub(crate) unsafe fn allocate_fresh_nonsync(&self, entity: Entity, world_slot: NonZeroU32) -> u32 {
        let new_slot = self.len.read_nonsync();
        self.len.write_nonsync(new_slot + 1);
        if new_slot as usize >= self.entities.len_nonsync() {
            self.grow_nonsync(64, world_slot);
        }
        self.entities[new_slot as usize].write_nonsync(entity);
        new_slot
    }

    /// Make room for `additional` more slots (free-listed slots count) with
    /// at most one growth.
    ///
    /// # Safety
    /// NS.
    pub(crate) unsafe fn reserve_nonsync(&self, additional: u32, world_slot: NonZeroU32) {
        let needed = additional.saturating_sub(self.num_free.read_nonsync());
        let spare = self.entities.len_nonsync() as u32 - self.len.read_nonsync();
        if needed > spare {
            self.grow_nonsync(needed - spare, world_slot);
        }
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
    ///
    /// # Safety
    /// NS, and `world_slot` is the owning world's.
    unsafe fn grow_nonsync(&self, min_increment: u32, world_slot: NonZeroU32) {
        let archetype_ptr = self as *const Archetype;
        // Double capacity or increase it by `min_increment`, whichever is larger.
        let additional = self.capacity().max(min_increment) as usize;
        let new_cap = self.entities.len() + additional;
        self.entities
            .extend_with_nonsync(additional, EntityCell::free());

        for (column, data) in self.data.iter().enumerate() {
            let entities_per_chunk = data.entities_per_chunk;
            let num_chunks_required = new_cap / entities_per_chunk + 1;
            let new_chunks = num_chunks_required.saturating_sub(data.storage.len());
            for _ in 0..new_chunks {
                unsafe {
                    let mem = data.new_chunk(archetype_ptr, world_slot, data.storage.len(), column);
                    data.storage.push_nonsync(mem);
                }
            }
        }
    }

    /// Increase capacity by at least `min_increment`
    fn grow(&mut self, min_increment: u32, world_slot: NonZeroU32) {
        let archetype_ptr = self as *const Archetype;
        // Double capacity or increase it by `min_increment`, whichever is larger.
        let additional = self.capacity().max(min_increment) as usize;
        let new_cap = self.entities.len() + additional;
        self.entities.extend_with(additional, EntityCell::free());

        for (column, data) in self.data.iter_mut().enumerate() {
            let entities_per_chunk = data.entities_per_chunk;
            let num_chunks_required = new_cap / entities_per_chunk + 1;
            let new_chunks = num_chunks_required.saturating_sub(data.storage.len());
            for _ in 0..new_chunks {
                unsafe {
                    let mem = data.new_chunk(archetype_ptr, world_slot, data.storage.len(), column);
                    data.storage.push(mem);
                }
            }
        }
    }

    /// Drop (or leave pending dead) every component of row `index` and free its entity cell.
    ///
    /// # Safety
    /// `index` is an occupied row whose entity was already retired; no column borrows on it.
    pub(crate) unsafe fn remove(&mut self, index: u32) {
        for (ty, data) in self.types.iter().zip(&*self.data) {
            let mut to_remove = data.get_gc_ptr(index);
            to_remove.drop_value_and_tombstone(ty);
        }
        self.entities[index as usize].set_free();
    }
    /// [`remove`](Self::remove) through `&self`.
    ///
    /// # Safety
    /// As [`remove`](Self::remove), plus NS.
    pub(crate) unsafe fn remove_nonsync(&self, index: u32) {
        for (ty, data) in self.types.iter().zip(&*self.data) {
            let mut to_remove = data.get_gc_ptr(index);
            to_remove.drop_value_and_tombstone(ty);
        }
        self.entities[index as usize].write_free_nonsync();
    }

    /// Returns the ID of the entity moved into `index`, if any
    ///
    /// # Safety
    /// NS; `index` is an occupied row; `f` must move each slot it is given (or leave it to
    /// the caller, who already tombstoned it), and only movable ones.
    pub(crate) unsafe fn move_to(
        &self,
        index: u32,
        mut f: impl FnMut(GCPtr, &TypeInfo),
    ) -> Option<u32> {
        for (ty, data) in self.types.iter().zip(&*self.data) {
            let gc_ptr = data.get_gc_ptr(index);
            f(gc_ptr, ty);
            self.entities[index as usize].write_free_nonsync();
        }
        None
    }

    /// Move the value at `component_data` into `ty`'s column at `index`.
    ///
    /// # Safety
    /// As [`GCPtr::move_from_value`]: NS, the slot is free (freshly allocated), and
    /// `component_data` points to a valid `ty` the caller then forgets.
    pub(crate) unsafe fn put_new_dynamic_nonsync(
        &self,
        component_data: *mut u8,
        ty: &TypeInfo,
        index: u32,
    ) {
        let mut ptr = self.get_dynamic(ty, index).unwrap();
        ptr.move_from_value(ty, component_data);
    }

    /// Move `gc_ptr`'s value into `ty`'s column at `index`.
    ///
    /// # Safety
    /// As [`GCPtr::move_from`]: NS, the target slot is free, and `gc_ptr` is movable (checked
    /// by the caller before the operation changed anything).
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
    ///
    /// When implementing this: each chunk's `StorageHeader::archetype`
    /// back-pointer is bound to its original owning archetype. If chunks are
    /// carried across from `other`, every header must be rewritten to point at
    /// `self`, otherwise `GCPtr::archetype()` and the sibling/entity_id
    /// helpers built on it will dereference a dropped archetype.
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

    /// How many times the sweep has freed row `slot` (wrapping below `u32::MAX`). While it is
    /// unchanged, a tombstone in the row is the one its last entity left.
    ///
    /// # Safety
    /// No concurrent structural change of this archetype.
    pub unsafe fn row_generation(&self, slot: u32) -> u32 {
        self.row_gens.get(slot)
    }

    /// What row `slot` holds when no entity occupies it: `None` for an occupied row, one past
    /// the allocated rows, or a mixed one (a column `Alive`, pending its drop).
    ///
    /// # Safety
    /// No concurrent structural change of this archetype.
    pub unsafe fn vacancy(&self, slot: u32) -> Option<Vacancy> {
        if slot >= self.len.read_nonsync() || self.entities[slot as usize].read_id_nonsync() != u32::MAX {
            return None;
        }
        let mut free = 0;
        for data in &*self.data {
            match gch::state(data.header(slot).get()) {
                gch::FREE => free += 1,
                gch::DEAD | gch::MOVED => {}
                _ => return None,
            }
        }
        match free {
            0 => Some(Vacancy::Tombstone),
            n if n == self.data.len() => Some(Vacancy::Free),
            _ => None,
        }
    }

    /// Take the `Free` rows among `rows` off the free list, leaving each an unreferenced
    /// tombstone (every column `Dead`, unmarked): a revive can claim it, and if none does, the
    /// next sweep frees it again. Rows not `Free` are skipped. Returns how many were taken. One
    /// pass over the free-row stack, a binary search of `rows` per free row.
    ///
    /// # Safety
    /// NS; nothing else allocates in or sweeps this archetype during the call. `rows` is
    /// sorted ascending.
    pub(crate) unsafe fn take_free_rows_nonsync(&self, rows: &[u32], world_slot: NonZeroU32) -> u32 {
        debug_assert!(rows.windows(2).all(|w| w[0] <= w[1]), "rows sorted");
        if self.data.is_empty() || rows.is_empty() {
            return 0;
        }
        let dead = gch::tombstone(gch::DEAD, crate::gc::mark_parity(world_slot));
        let mut taken = 0;
        (*self.free_rows.0.get()).retain(|&slot| {
            if rows.binary_search(&slot).is_err() {
                return true;
            }
            for data in &*self.data {
                let word = data.header(slot);
                debug_assert_eq!(gch::state(word.get()), gch::FREE, "value in free list but state is not free");
                word.set(dead);
            }
            taken += 1;
            false
        });
        self.num_free.write_nonsync(self.num_free.read_nonsync() - taken);
        taken
    }

    /// Put row `slot` on the free list (every column `Free`), counting a new
    /// [`row_generation`](Self::row_generation).
    ///
    /// # Safety
    /// NS; `slot` is below the allocated slots, its entity cell is free, and every column is
    /// `Dead` or `Moved` and unreferenced (the sweep checks this): no `GCPtr` to it is used again.
    pub(crate) unsafe fn free_slot(&self, slot: u32) {
        self.row_gens.bump(slot);
        let current_num_free = self.num_free.read_nonsync();
        self.num_free.write_nonsync(current_num_free + 1);
        debug_assert!(
            self.len.read_nonsync() >= current_num_free + 1,
            "allocated len is {} and num free is {}",
            self.len.read_nonsync(),
            current_num_free + 1
        );
        for data in self.data.iter() {
            // One address computation per cell: the word and the forwarding entry share it.
            let (sh, index) = data.cell(slot);
            let word = crate::gc::word_at(sh, index);
            let w = word.get();
            debug_assert!(
                matches!(gch::state(w), gch::DEAD | gch::MOVED) && gch::is_movable(w & !gch::STATE_MASK),
                "freeing a cell in state {}",
                word.state_name()
            );
            if gch::state(w) == gch::MOVED {
                crate::gc::clear_moved_at(sh, index);
            }
            word.set(gch::FREE_WORD);
        }
        self.free_rows.push(slot);
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
                    let word = data.header(index);
                    let is_free = gch::state(word.get()) == gch::FREE;
                    #[cfg(debug_assertions)]
                    if !is_free {
                        if !std::thread::panicking() {
                            std::eprintln!(
                                "Archetype storage dropped without freeing dead values: {:?} at id {} was {:?}",
                                info, index, word
                            );
                        }
                    }
                    let _ = info;
                    needs_leak |= !is_free;
                }
            }
            if !needs_leak {
                for chunk in data.chunks() {
                    assert!(!chunk.is_null());
                    unsafe {
                        (*chunk.cast::<StorageHeader>()).free_forward_table();
                        dealloc(*chunk, data.storage_layout);
                    }
                }
            }
        }
        self.data = Box::default();
    }
}

pub const DATA_CHUNK_SIZE_BYTES: usize = CHUNK_BYTES;

/// The first bytes of every column chunk (see [`crate::gc::header`] for the chunk layout).
/// `repr(C)`: newgameplus-api reads `forward`, `values_start`, `stride` and `recip` at the
/// offsets of [`ChunkAbi`](crate::gc::header::ChunkAbi).
#[repr(C)]
pub(crate) struct StorageHeader {
    /// Back-pointer to the owning archetype. Stable because archetypes live in
    /// a `SharedVec<Archetype>` whose elements never relocate, and chunks are
    /// only allocated after the archetype is placed in the vec.
    pub(crate) archetype: *const Archetype,
    /// The forwarding table of the chunk's `Moved` cells: `capacity` value pointers indexed like
    /// the header words; null while no cell of the chunk is `Moved`.
    pub(crate) forward: Cell<*mut *mut u8>,
    pub(crate) world_slot: NonZeroU32,
    /// `Moved` cells in this chunk (the forwarding table lives while this is nonzero).
    pub(crate) moved: Cell<u32>,
    pub(crate) chunk_idx: u32,
    pub(crate) capacity: u32,
    pub(crate) values_start: u32,
    pub(crate) stride: u32,
    pub(crate) recip: u64,
    /// This chunk's column in its archetype (`archetype.types()[column]`).
    pub(crate) column: u32,
}

const _: () = {
    use crate::gc::header::ChunkAbi;
    assert!(core::mem::offset_of!(StorageHeader, forward) == ChunkAbi::FORWARD);
    assert!(core::mem::offset_of!(StorageHeader, values_start) == ChunkAbi::VALUES_START);
    assert!(core::mem::offset_of!(StorageHeader, stride) == ChunkAbi::STRIDE);
    assert!(core::mem::offset_of!(StorageHeader, recip) == ChunkAbi::RECIP);
    assert!(core::mem::size_of::<StorageHeader>() <= HEADERS_OFFSET);
};

impl StorageHeader {
    fn forward_layout(&self) -> Layout {
        Layout::array::<*mut u8>(self.capacity as usize).unwrap()
    }

    /// The forwarding table, allocated if the chunk has none (uninitialized: an entry is read
    /// only while its cell is `Moved`, after `set_moved` wrote it; no zeroing, so a large table
    /// touches only the pages its `Moved` cells use).
    ///
    /// # Safety
    /// NS.
    #[inline]
    pub(crate) unsafe fn forward_table_or_alloc(&self) -> *mut *mut u8 {
        let table = self.forward.get();
        if !table.is_null() {
            return table;
        }
        let table = alloc(self.forward_layout()).cast::<*mut u8>();
        assert!(!table.is_null(), "allocation failed");
        self.forward.set(table);
        table
    }

    /// Free the forwarding table, if any.
    ///
    /// # Safety
    /// NS; no cell of the chunk is `Moved`.
    pub(crate) unsafe fn free_forward_table(&self) {
        let table = self.forward.replace(null_mut());
        if !table.is_null() {
            dealloc(table.cast(), self.forward_layout());
        }
    }
}

/// One column of an archetype: its 64 KiB chunks and their [geometry](Geometry).
pub struct Data {
    storage: KVec<*mut u8>,
    storage_layout: Layout,
    state: AtomicBorrow,
    stride: usize,
    values_start: usize,
    entities_per_chunk: usize,
    recip: u64,
}

impl Data {
    /// Allocate and initialise a chunk: its storage header, and every header word `Free`.
    ///
    /// # Safety
    /// `archetype` owns this column.
    unsafe fn new_chunk(
        &self,
        archetype: *const Archetype,
        world_slot: NonZeroU32,
        chunk_idx: usize,
        column: usize,
    ) -> *mut u8 {
        let mem = alloc(self.storage_layout);
        assert!(!mem.is_null(), "allocation failed");
        // Zero the header region and the padding up to the values; leave the values
        // uninitialised.
        ptr::write_bytes(mem, 0, self.values_start);
        mem.cast::<StorageHeader>().write(StorageHeader {
            archetype,
            forward: Cell::new(null_mut()),
            world_slot,
            moved: Cell::new(0),
            chunk_idx: chunk_idx as u32,
            capacity: self.entities_per_chunk as u32,
            values_start: self.values_start as u32,
            stride: self.stride as u32,
            recip: self.recip,
            column: column as u32,
        });
        let words = mem.add(HEADERS_OFFSET).cast::<u32>();
        for i in 0..self.entities_per_chunk {
            words.add(i).write(gch::FREE_WORD);
        }
        mem
    }

    #[inline(always)]
    pub fn chunks(&self) -> &[*mut u8] {
        &self.storage
    }
    /// Bytes per value (the size rounded up to the alignment; a zero-sized type's alignment).
    #[inline(always)]
    pub fn stride(&self) -> usize {
        self.stride
    }
    /// Offset of value 0 from the start of each chunk (past the chunk header and the header
    /// words).
    #[inline(always)]
    pub fn values_start(&self) -> usize {
        self.values_start
    }
    /// Cells per chunk; cell `i` lives in chunk `i / entities_per_chunk`.
    #[inline(always)]
    pub fn entities_per_chunk(&self) -> usize {
        self.entities_per_chunk
    }

    /// The value pointer of cell `idx`.
    ///
    /// # Safety
    /// `idx` has a chunk: `idx < chunks().len() * entities_per_chunk()`, which holds for any
    /// `idx` below the archetype's allocated slot count. Dereferencing the result needs NS or
    /// STRUCT, and a borrow of the cell as for any [`GCPtr`].
    #[inline(always)]
    pub unsafe fn value_ptr(&self, idx: u32) -> NonNull<u8> {
        let idx = idx as usize;
        NonNull::new_unchecked(
            self.storage
                .get_unchecked(idx / self.entities_per_chunk)
                .add(self.values_start + (idx % self.entities_per_chunk) * self.stride),
        )
    }

    /// The header word of cell `idx`.
    ///
    /// # Safety
    /// As [`value_ptr`](Self::value_ptr); the reference must not outlive the chunk.
    #[inline(always)]
    pub unsafe fn header<'a>(&self, idx: u32) -> &'a HeaderWord {
        let idx = idx as usize;
        &*self
            .storage
            .get_unchecked(idx / self.entities_per_chunk)
            .add(HEADERS_OFFSET + (idx % self.entities_per_chunk) * HEADER_BYTES)
            .cast::<HeaderWord>()
    }

    /// Cell `idx`'s chunk header and index in the chunk (one 32-bit division), for several
    /// accesses to the cell (`gc::word_at`, `gc::value_at`, the forwarding entry).
    ///
    /// # Safety
    /// As [`value_ptr`](Self::value_ptr); the reference must not outlive the chunk.
    #[inline(always)]
    pub(crate) unsafe fn cell<'a>(&self, idx: u32) -> (&'a StorageHeader, usize) {
        let per = self.entities_per_chunk as u32;
        (
            &*self.storage.get_unchecked((idx / per) as usize).cast::<StorageHeader>(),
            (idx % per) as usize,
        )
    }

    /// The header words of chunk `chunk` (all `entities_per_chunk` of them).
    ///
    /// # Safety
    /// `chunk < chunks().len()`; the slice must not outlive the chunk.
    #[inline(always)]
    pub unsafe fn chunk_headers<'a>(&self, chunk: usize) -> &'a [HeaderWord] {
        core::slice::from_raw_parts(
            self.storage.get_unchecked(chunk).add(HEADERS_OFFSET).cast::<HeaderWord>(),
            self.entities_per_chunk,
        )
    }

    /// The [`GCPtr`] of cell `idx`.
    ///
    /// # Safety
    /// As [`value_ptr`](Self::value_ptr).
    #[inline(always)]
    pub unsafe fn get_gc_ptr(&self, idx: u32) -> GCPtr {
        GCPtr::from_raw(self.value_ptr(idx))
    }

    /// The value pointer of cell `idx`.
    ///
    /// # Safety
    /// As [`value_ptr`](Self::value_ptr).
    #[inline(always)]
    pub(crate) unsafe fn get_value(&self, idx: u32) -> NonNull<u8> {
        self.value_ptr(idx)
    }

    /// Disarm every armed cell in `first..end` ([`HeaderWord::disarm`] over the dense words,
    /// in blocks: a block with no armed cell is only read). Returns the number disarmed.
    ///
    /// # Safety
    /// NS; `end` is at most the archetype's allocated slots.
    pub unsafe fn disarm_range(&self, first: u32, end: u32) -> u64 {
        const BLOCK: usize = 16;
        let per = self.entities_per_chunk;
        let mut disarmed = 0u64;
        let mut i = first as usize;
        let end = end as usize;
        while i < end {
            let chunk = i / per;
            let lo = i % per;
            let hi = per.min(lo + (end - i));
            let words = &self.chunk_headers(chunk)[lo..hi];
            for block in words.chunks(BLOCK) {
                let mut n = 0u32;
                for w in block {
                    n += gch::needs_disarm(w.get()) as u32;
                }
                if n != 0 {
                    for w in block {
                        let v = w.get();
                        // Branch-free: clear ARMED where armed.
                        w.set(v & !(gch::ARMED * gch::needs_disarm(v) as u32));
                    }
                    disarmed += n as u64;
                }
            }
            i += hi - lo;
        }
        disarmed
    }

    /// Call `visit(cell, word)` for every cell below `count` whose header word passes
    /// `filter`. Reads the dense header words in blocks of 16 (`filter` ORed over a block, which
    /// the compiler vectorizes for a branch-free `filter`) and visits only blocks with a hit, so
    /// a column with few candidates costs one pass of streaming loads over its headers.
    /// `visit` may rewrite the word it is given.
    ///
    /// # Safety
    /// NS; `count` is at most the archetype's allocated slots.
    #[inline]
    pub(crate) unsafe fn scan_headers(
        &self,
        count: u32,
        filter: impl Fn(u32) -> bool,
        mut visit: impl FnMut(u32, &HeaderWord),
    ) {
        const BLOCK: usize = 16;
        let count = count as usize;
        let per = self.entities_per_chunk;
        let mut base = 0usize;
        let mut chunk = 0usize;
        while base < count {
            let n = per.min(count - base);
            let words = &self.chunk_headers(chunk)[..n];
            let mut start = 0;
            for block in words.chunks(BLOCK) {
                let mut hit = false;
                for w in block {
                    hit |= filter(w.get());
                }
                if hit {
                    for (i, w) in block.iter().enumerate() {
                        if filter(w.get()) {
                            visit((base + start + i) as u32, w);
                        }
                    }
                }
                start += block.len();
            }
            base += per;
            chunk += 1;
        }
    }
}

/// A no-op identity hasher for pre-hashed u64 keys (StableTypeId, TypeId).
///
/// Both StableTypeId (FNV-1a output) and std TypeId are well-distributed u64s,
/// so re-hashing is unnecessary.
#[derive(Default)]
pub(crate) struct IdentityHasher {
    hash: u64,
}

impl Hasher for IdentityHasher {
    fn write_u64(&mut self, n: u64) {
        debug_assert_eq!(self.hash, 0);
        self.hash = n;
    }

    fn write_u128(&mut self, n: u128) {
        debug_assert_eq!(self.hash, 0);
        self.hash = n as u64;
    }

    fn write(&mut self, bytes: &[u8]) {
        debug_assert_eq!(self.hash, 0);
        let mut hasher = <DefaultHashBuilder as BuildHasher>::Hasher::default();
        hasher.write(bytes);
        self.hash = hasher.finish();
    }

    fn finish(&self) -> u64 {
        self.hash
    }
}

/// A HashMap with StableTypeId keys (for component type lookups).
pub(crate) type StableTypeIdMap<V> = HashMap<StableTypeId, V, BuildHasherDefault<IdentityHasher>>;

/// A HashMap with std TypeId keys (for bundle identity caching).
pub(crate) type TypeIdMap<V> = HashMap<core::any::TypeId, V, BuildHasherDefault<IdentityHasher>>;

struct OrderedTypeIdMap<V>(Box<[(StableTypeId, V)]>);

impl<V> OrderedTypeIdMap<V> {
    fn new(iter: impl Iterator<Item = (StableTypeId, V)>) -> Self {
        let mut vals = iter.collect::<Box<[_]>>();
        vals.sort_unstable_by_key(|(id, _)| *id);
        Self(vals)
    }

    fn search(&self, id: &StableTypeId) -> Option<usize> {
        self.0.binary_search_by_key(id, |(id, _)| *id).ok()
    }

    fn contains_key(&self, id: &StableTypeId) -> bool {
        self.search(id).is_some()
    }

    fn get(&self, id: &StableTypeId) -> Option<&V> {
        self.search(id).map(move |idx| &self.0[idx].1)
    }
}

/// Metadata required to store a component.
///
/// Stores a [`StableTypeId`] for cross-cdylib stable identification, a
/// [`Layout`] for memory allocation, and a drop function which internally
/// calls [`core::ptr::drop_in_place`] with the correct type parameter.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub(crate) id: StableTypeId,
    value_layout: Layout,
    geometry: Geometry,
    drop: DropFn,
    #[cfg(debug_assertions)]
    pub(crate) type_name: &'static str,
}

impl TypeInfo {
    /// Construct a `TypeInfo` directly from a component type.
    pub fn of<T: Component>() -> Self {
        unsafe fn drop_ptr<T>(x: *mut u8) {
            x.cast::<T>().drop_in_place()
        }

        let type_layout = Layout::new::<T>();
        Self {
            id: T::STABLE_TYPE_ID,
            value_layout: type_layout,
            geometry: gch::TypedGeometry::<T>::GEOMETRY,
            drop: DropFn::Typed(drop_ptr::<T>),
            #[cfg(debug_assertions)]
            type_name: core::any::type_name::<T>(),
        }
    }

    /// Construct a `TypeInfo` from its components. This is useful in the rare case that you have
    /// some kind of pointer to raw bytes/erased memory holding a component type, coming from a
    /// source unrelated to hecs, and you want to treat it as an insertable component by
    /// implementing the `DynamicBundle` API.
    pub fn from_parts(id: StableTypeId, layout: Layout, drop: unsafe fn(*mut u8)) -> Self {
        Self::from_parts_with(id, layout, DropFn::Typed(drop))
    }

    /// Like [`TypeInfo::from_parts`], but the destructor receives the component's
    /// [`StableTypeId`] and resolves the real drop at call time. For component types whose
    /// code can be unloaded and reloaded (hot-reloaded modules), where a per-type function
    /// pointer captured at insert time would dangle.
    pub fn from_parts_by_id(
        id: StableTypeId,
        layout: Layout,
        drop: unsafe fn(StableTypeId, *mut u8),
    ) -> Self {
        Self::from_parts_with(id, layout, DropFn::ById(drop))
    }

    fn from_parts_with(id: StableTypeId, layout: Layout, drop: DropFn) -> Self {
        Self {
            id,
            value_layout: layout,
            geometry: Geometry::of(layout.size(), layout.align()),
            drop,
            #[cfg(debug_assertions)]
            type_name: "<unknown> (TypeInfo constructed from parts)",
        }
    }

    /// Access the `StableTypeId` for this component type.
    pub fn id(&self) -> StableTypeId {
        self.id
    }

    /// Access the `Layout` of this component type.
    pub fn value_layout(&self) -> Layout {
        self.value_layout
    }

    /// Where this type's cells sit in a column chunk (a function of its layout alone).
    pub fn geometry(&self) -> Geometry {
        self.geometry
    }

    /// The alignment archetypes order columns by: the value's, at least 8 (the order the
    /// interleaved 8-aligned header gave, kept so archetype type orders are unchanged).
    fn sort_align(&self) -> usize {
        self.value_layout.align().max(8)
    }

    /// Directly call the destructor on a pointer to data of this component type.
    ///
    /// # Safety
    ///
    /// All of the caveats of [`core::ptr::drop_in_place`] apply, with the additional requirement
    /// that this method is being called on a pointer to an object of the correct component type.
    /// No `&` or `&mut` to the value may be live (or used afterwards), and it is never dropped
    /// twice: a slot's value is dropped by exactly one of `drop_value_and_tombstone` or, for a
    /// slot left pending dead under a gc guard, `gc::sweep`.
    pub unsafe fn drop_value(&self, data: *mut u8) {
        match self.drop {
            DropFn::Typed(f) => f(data),
            DropFn::ById(f) => f(self.id, data),
        }
    }

    /// The destructor for the component type this `TypeInfo` represents.
    pub fn drop_shim(&self) -> DropFn {
        self.drop
    }
}

/// A component destructor: either a per-type function, or one shared function that dispatches
/// on the [`StableTypeId`] at call time.
#[derive(Debug, Clone, Copy)]
pub enum DropFn {
    Typed(unsafe fn(*mut u8)),
    ById(unsafe fn(StableTypeId, *mut u8)),
}

/// The `(alignment, id)` key that `TypeInfo`'s `Ord` sorts `T` by, without building a `TypeInfo`.
/// Static bundles sort their ids with it so every spawn path keys a type set in one order.
#[doc(hidden)]
pub fn type_sort_key<T: Component>() -> (usize, StableTypeId) {
    (core::mem::align_of::<T>().max(8), T::STABLE_TYPE_ID)
}

impl PartialOrd for TypeInfo {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypeInfo {
    /// Order by alignment, descending. Ties broken with TypeId.
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.sort_align()
            .cmp(&other.sort_align())
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

#[cfg(test)]
mod drop_fn_tests {
    use super::*;
    use core::sync::atomic::{AtomicU64, Ordering};

    static SEEN: AtomicU64 = AtomicU64::new(0);

    unsafe fn record(id: StableTypeId, _data: *mut u8) {
        SEEN.store(id.0, Ordering::SeqCst);
    }

    #[test]
    fn by_id_drop_receives_type_id() {
        let ty = TypeInfo::from_parts_by_id(StableTypeId(42), Layout::new::<u32>(), record);
        let mut value = 7u32;
        unsafe { ty.drop_value((&mut value as *mut u32).cast()) };
        assert_eq!(SEEN.load(Ordering::SeqCst), 42);
    }
}
