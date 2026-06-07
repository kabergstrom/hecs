// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::alloc::{vec, vec::Vec};
use crate::gc::cells::PtrCell;
use crate::gc::kvec::KVec;
use crate::gc::{alloc_world_slot, free_world_slot};
use core::any::TypeId;
use core::borrow::Borrow;
use core::cell::{Cell, UnsafeCell};
use core::convert::TryFrom;
use core::hash::{BuildHasherDefault, Hasher};
use core::num::NonZeroU32;
#[cfg(feature = "mirror_mirror")]
use mirror_mirror::Reflect;
use spin::Mutex;

use core::{fmt, ptr};

#[cfg(feature = "std")]
use std::error::Error;

use hashbrown::hash_map::{Entry, HashMap};

use crate::alloc::boxed::Box;
use crate::archetype::{Archetype, TypeIdMap, TypeInfo};
use crate::entities::{Entities, EntityMeta, Location, ReserveEntitiesIterator};
use crate::{
    sharedvec, Bundle, CRef, ColumnBatch, ComponentRef, DynamicBundle, Entity, EntityRef, Fetch,
    MissingComponent, NoSuchEntity, Query, QueryBorrow, QueryItem, QueryMut, QueryOne, TakenEntity,
};

/// An unordered collection of entities, each having any number of distinctly typed components
///
/// Similar to `HashMap<Entity, Vec<Box<dyn Any>>>` where each `Vec` never contains two of the same
/// type, but far more efficient to traverse.
///
/// The components of entities who have the same set of component types are stored in contiguous
/// runs, allowing for extremely fast, cache-friendly iteration.
///
/// There is a maximum number of unique entity IDs, which means that there is a maximum number of live
/// entities. When old entities are despawned, their IDs will be reused on a future entity, and
/// old `Entity` values with that ID will be invalidated.
///
/// ### Collisions
///
/// If an entity is despawned and its `Entity` handle is preserved over the course of billions of
/// following spawns and despawns, that handle may, in rare circumstances, collide with a
/// newly-allocated `Entity` handle. Very long-lived applications should therefore limit the period
/// over which they may retain handles of despawned entities.
pub struct World {
    entities: Entities,
    archetypes: ArchetypeSet,
    /// Maps statically-typed bundle types to archetypes
    bundle_to_archetype: NonSyncCell<TypeIdMap<sharedvec::DefaultKey>>,
    /// Maps source archetype and static bundle types to the archetype that an entity is moved to
    /// after inserting the components from that bundle.
    insert_edges: NonSyncCell<IndexTypeIdMap<InsertTarget>>,
    /// Maps source archetype and static bundle types to the archetype that an entity is moved to
    /// after removing the components from that bundle.
    remove_edges: NonSyncCell<IndexTypeIdMap<sharedvec::DefaultKey>>,
    id: u64,
    world_slot: NonZeroU32,
}
impl Drop for World {
    fn drop(&mut self) {
        unsafe { free_world_slot(self.world_slot) };
    }
}

struct NonSyncCell<T>(UnsafeCell<T>);
unsafe impl<T> Sync for NonSyncCell<T> {}

impl World {
    /// Create an empty world
    pub fn new() -> Self {
        // AtomicU64 is unsupported on 32-bit MIPS and PPC architectures
        // For compatibility, use Mutex<u64>
        static ID: Mutex<u64> = Mutex::new(1);
        let id = {
            let mut id = ID.lock();
            let next = id.checked_add(1).unwrap();
            *id = next;
            next
        };
        Self {
            entities: Entities::default(),
            archetypes: ArchetypeSet::new(),
            bundle_to_archetype: NonSyncCell(UnsafeCell::new(HashMap::default())),
            insert_edges: NonSyncCell(UnsafeCell::new(HashMap::default())),
            remove_edges: NonSyncCell(UnsafeCell::new(HashMap::default())),
            id,
            world_slot: alloc_world_slot(),
        }
    }

    /// Create an entity with certain components
    ///
    /// Returns the ID of the newly created entity.
    ///
    /// Arguments can be tuples, structs annotated with [`#[derive(Bundle)]`](macro@Bundle), or the
    /// result of calling [`build`](crate::EntityBuilder::build) on an
    /// [`EntityBuilder`](crate::EntityBuilder), which is useful if the set of components isn't
    /// statically known. To spawn an entity with only one component, use a one-element tuple like
    /// `(x,)`.
    ///
    /// Any type that satisfies `Send + Sync + 'static` can be used as a component.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, "abc".to_string()));
    /// let b = world.spawn((456, true));
    /// ```
    pub fn spawn(&mut self, components: impl DynamicBundle) -> Entity {
        // Ensure all entity allocations are accounted for so `self.entities` can realloc if
        // necessary
        self.flush();

        let entity = self.entities.alloc();

        self.spawn_inner(entity, components);

        entity
    }

    pub unsafe fn spawn_nonsync(&self, components: impl DynamicBundle) -> Entity {
        // Ensure all entity allocations are accounted for so `self.entities` can realloc if
        // necessary
        self.flush_nonsync();

        let entity = self.entities.alloc_nonsync();

        self.spawn_inner_nonsync(entity, components);

        entity
    }

    /// Create an entity with certain components and a specific [`Entity`] handle.
    ///
    /// See [`spawn`](Self::spawn).
    ///
    /// Despawns any existing entity with the same [`Entity::id`].
    ///
    /// Useful for easy handle-preserving deserialization. Be cautious resurrecting old `Entity`
    /// handles in already-populated worlds as it vastly increases the likelihood of collisions.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, "abc".to_string()));
    /// let b = world.spawn((456, true));
    /// world.despawn(a);
    /// assert!(!world.contains(a));
    /// // all previous Entity values pointing to 'a' will be live again, instead pointing to the new entity.
    /// world.spawn_at(a, (789, "abc".to_string()));
    /// assert!(world.contains(a));
    /// ```
    pub fn spawn_at(&mut self, handle: Entity, components: impl DynamicBundle) {
        // Ensure all entity allocations are accounted for so `self.entities` can realloc if
        // necessary
        self.flush();

        let loc = self.entities.alloc_at(handle);
        if let Some(loc) = loc {
            unsafe { self.archetypes.archetypes[loc.archetype].remove(loc.index) }
        }

        self.spawn_inner(handle, components);
    }

    fn spawn_inner(&mut self, entity: Entity, components: impl DynamicBundle) {
        let archetype_id = match components.key() {
            Some(k) => {
                let archetypes = &mut self.archetypes;
                let bundle_to_archetype = self.bundle_to_archetype.0.get_mut();

                *bundle_to_archetype.entry(k).or_insert_with(|| {
                    components.with_ids(|ids| archetypes.get(ids, || components.type_info()))
                })
            }
            None => components.with_ids(|ids| self.archetypes.get(ids, || components.type_info())),
        };

        let archetype = &mut self.archetypes.archetypes[archetype_id];
        // SAFETY: we have &mut self
        unsafe {
            let index = archetype.allocate_nonsync(entity, self.world_slot);
            components.put(|ptr, ty| {
                archetype.put_new_dynamic_nonsync(ptr, &ty, index);
            });
            self.entities.meta[entity.id as usize].location = Location {
                archetype: archetype_id,
                index,
            };
        }
    }
    unsafe fn spawn_inner_nonsync(&self, entity: Entity, components: impl DynamicBundle) {
        let archetype_id = match components.key() {
            Some(k) => {
                let archetypes = &self.archetypes;

                // we have &self here, but we never return any references elsewhere so we can grab a &mut of bundle_to_archetype
                // since we're in a !Sync context
                let bundle_to_archetype_ptr = self.bundle_to_archetype.0.get();
                let bundle_to_archetype = bundle_to_archetype_ptr.as_mut().unwrap();

                *bundle_to_archetype.entry(k).or_insert_with(|| {
                    components
                        .with_ids(|ids| archetypes.get_nonsync(ids, || components.type_info()))
                })
            }
            None => components
                .with_ids(|ids| self.archetypes.get_nonsync(ids, || components.type_info())),
        };

        let archetype = &self.archetypes.archetypes[archetype_id];
        // SAFETY: we have &mut self
        unsafe {
            let index = archetype.allocate_nonsync(entity, self.world_slot);
            components.put(|ptr, ty| {
                archetype.put_new_dynamic_nonsync(ptr, &ty, index);
            });
            self.entities.meta.set_nonsync(
                entity.id as usize,
                EntityMeta {
                    generation: entity.generation,
                    location: Location {
                        archetype: archetype_id,
                        index,
                    },
                },
            );
        }
    }

    /// Efficiently spawn a large number of entities with the same statically-typed components
    ///
    /// Faster than calling [`spawn`](Self::spawn) repeatedly with the same components, but requires
    /// that component types are known at compile time.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let entities = world.spawn_batch((0..1_000).map(|i| (i, "abc".to_string()))).collect::<Vec<_>>();
    /// for i in 0..1_000 {
    ///     assert_eq!(*world.get::<&i32>(entities[i]).unwrap(), i as i32);
    /// }
    /// ```
    pub fn spawn_batch<I>(&mut self, iter: I) -> SpawnBatchIter<'_, I::IntoIter>
    where
        I: IntoIterator,
        I::Item: Bundle + 'static,
    {
        // Ensure all entity allocations are accounted for so `self.entities` can realloc if
        // necessary
        self.flush();

        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();
        let archetype_id = self.reserve_inner::<I::Item>(
            u32::try_from(upper.unwrap_or(lower)).expect("iterator too large"),
        );

        SpawnBatchIter {
            inner: iter,
            entities: &mut self.entities,
            archetype_id,
            archetype: &mut self.archetypes.archetypes[archetype_id],
            world_slot: &self.world_slot,
        }
    }

    /// Super-efficiently spawn the contents of a [`ColumnBatch`]
    ///
    /// The fastest, but most specialized, way to spawn large numbers of entities. Useful for high
    /// performance deserialization. Supports dynamic component types.
    pub fn spawn_column_batch(&mut self, batch: ColumnBatch) -> SpawnColumnBatchIter<'_> {
        self.flush();

        let archetype = batch.0;
        // SAFETY: We have &mut self
        let entity_count = unsafe { archetype.allocated_values_nonsync() };
        // Store component data
        let (archetype_id, base) = self.archetypes.insert_batch(archetype);

        let archetype = &mut self.archetypes.archetypes[archetype_id];
        let id_alloc = self.entities.alloc_many(entity_count, archetype_id, base);

        // Fix up entity IDs
        let mut id_alloc_clone = id_alloc.clone();
        let mut index = base as usize;
        while let Some(id) = id_alloc_clone.next(&self.entities) {
            let entity = unsafe { self.entities.resolve_unknown_gen(id) };
            archetype.set_entity(index, entity);
            index += 1;
        }

        // Return iterator over new IDs
        SpawnColumnBatchIter {
            pending_end: id_alloc.pending_end,
            id_alloc,
            entities: &mut self.entities,
        }
    }

    /// Hybrid of [`spawn_column_batch`](Self::spawn_column_batch) and [`spawn_at`](Self::spawn_at)
    pub fn spawn_column_batch_at(&mut self, handles: &[Entity], batch: ColumnBatch) {
        let archetype = batch.0;
        assert_eq!(
            handles.len(),
            archetype.allocated_values_sync() as usize,
            "number of entity IDs {} must match number of entities {}",
            handles.len(),
            archetype.allocated_values_sync()
        );

        // Drop components of entities that will be replaced
        for &handle in handles {
            let loc = self.entities.alloc_at(handle);
            if let Some(loc) = loc {
                unsafe { self.archetypes.archetypes[loc.archetype].remove(loc.index) }
            }
        }

        // Store components
        let (archetype_id, base) = self.archetypes.insert_batch(archetype);

        // Fix up entity IDs
        let archetype = &mut self.archetypes.archetypes[archetype_id];
        for (&handle, index) in handles.iter().zip(base as usize..) {
            archetype.set_entity(index, handle);
            self.entities.meta[handle.id() as usize].location = Location {
                archetype: archetype_id,
                index: index as u32,
            };
        }
    }

    /// Allocate many entities ID concurrently
    ///
    /// Unlike [`spawn`](Self::spawn), this can be called concurrently with other operations on the
    /// [`World`] such as queries, but does not immediately create the entities. Reserved entities
    /// are not visible to queries or world iteration, but can be otherwise operated on
    /// freely. Operations that add or remove components or entities, such as `insert` or `despawn`,
    /// will cause all outstanding reserved entities to become real entities before proceeding. This
    /// can also be done explicitly by calling [`flush`](Self::flush).
    ///
    /// Useful for reserving an ID that will later have components attached to it with `insert`.
    pub fn reserve_entities(&self, count: u32) -> ReserveEntitiesIterator {
        self.entities.reserve_entities(count)
    }

    /// Allocate an entity ID concurrently
    ///
    /// See [`reserve_entities`](Self::reserve_entities).
    pub fn reserve_entity(&self) -> Entity {
        self.entities.reserve_entity()
    }

    /// Destroy an entity and all its components
    ///
    /// See also [`take`](Self::take).
    pub fn despawn(&mut self, entity: Entity) -> Result<(), NoSuchEntity> {
        self.flush();
        let loc = self.entities.free(entity)?;
        unsafe { self.archetypes.archetypes[loc.archetype].remove(loc.index) }
        Ok(())
    }

    pub unsafe fn despawn_nonsync(&self, entity: Entity) -> Result<(), NoSuchEntity> {
        self.flush_nonsync();
        let loc = self.entities.retire_nonsync(entity)?;
        unsafe { self.archetypes.archetypes[loc.archetype].remove_nonsync(loc.index) }
        Ok(())
    }

    /// Ensure at least `additional` entities with exact components `T` can be spawned without reallocating
    pub fn reserve<T: Bundle + 'static>(&mut self, additional: u32) {
        self.reserve_inner::<T>(additional);
    }

    fn reserve_inner<T: Bundle + 'static>(&mut self, additional: u32) -> sharedvec::DefaultKey {
        self.flush();
        self.entities.reserve(additional);

        let archetypes = &mut self.archetypes;
        // SAFETY: we have &mut self
        let bundle_to_archetype = self.bundle_to_archetype.0.get_mut();
        let archetype_id = *bundle_to_archetype
            .entry(TypeId::of::<T>())
            .or_insert_with(|| {
                T::with_static_ids(|ids| {
                    archetypes.get(ids, || T::with_static_type_info(|info| info.to_vec()))
                })
            });

        self.archetypes.archetypes[archetype_id].reserve(additional, self.world_slot);
        archetype_id
    }

    /// Despawn all entities
    ///
    /// Preserves allocated storage for reuse but clears metadata so that [`Entity`] values will repeat (in contrast to [`despawn`][Self::despawn]).
    pub fn clear(&mut self) {
        for i in 0..self.archetypes.archetypes.len() {
            let key = self.archetypes.archetypes.key_from_index(i).unwrap();
            let x = self.archetypes.archetypes.get_mut(key).unwrap();
            x.clear();
        }
        self.entities.clear();
    }

    /// Whether `entity` still exists
    pub fn contains(&self, entity: Entity) -> bool {
        self.entities.contains(entity)
    }

    /// Efficiently iterate over all entities that have certain components, using dynamic borrow
    /// checking
    ///
    /// Prefer [`query_mut`](Self::query_mut) when concurrent access to the [`World`] is not required.
    ///
    /// Calling `iter` on the returned value yields `(Entity, Q)` tuples, where `Q` is some query
    /// type. A query type is any type for which an implementation of [`Query`] exists, e.g. `&T`,
    /// `&mut T`, a tuple of query types, or an `Option` wrapping a query type, where `T` is any
    /// component type. Components queried with `&mut` must only appear once. Entities which do not
    /// have a component type referenced outside of an `Option` will be skipped.
    ///
    /// Entities are yielded in arbitrary order.
    ///
    /// The returned [`QueryBorrow`] can be further transformed with combinator methods; see its
    /// documentation for details.
    ///
    /// Iterating a query will panic if it would violate an existing unique reference or construct
    /// an invalid unique reference. This occurs when two simultaneously-active queries could expose
    /// the same entity. Simultaneous queries can access the same component type if and only if the
    /// world contains no entities that have all components required by both queries, assuming no
    /// other component borrows are outstanding.
    ///
    /// Iterating a query yields references with lifetimes bound to the [`QueryBorrow`] returned
    /// here. To ensure those are invalidated, the return value of this method must be dropped for
    /// its dynamic borrows from the world to be released. Similarly, lifetime rules ensure that
    /// references obtained from a query cannot outlive the [`QueryBorrow`].
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, true, "abc".to_string()));
    /// let b = world.spawn((456, false));
    /// let c = world.spawn((42, "def".to_string()));
    /// let entities = world.query::<(&i32, &bool)>()
    ///     .iter()
    ///     .map(|(e, (&i, &b))| (e, i, b)) // Copy out of the world
    ///     .collect::<Vec<_>>();
    /// assert_eq!(entities.len(), 2);
    /// assert!(entities.contains(&(a, 123, true)));
    /// assert!(entities.contains(&(b, 456, false)));
    /// ```
    pub fn query<Q: Query>(&self) -> QueryBorrow<'_, Q> {
        QueryBorrow::new(&self.entities.meta, &self.archetypes.archetypes)
    }

    /// Query a uniquely borrowed world
    ///
    /// Like [`query`](Self::query), but faster because dynamic borrow checks can be skipped. Note
    /// that, unlike [`query`](Self::query), this returns an `IntoIterator` which can be passed
    /// directly to a `for` loop.
    pub fn query_mut<Q: Query>(&mut self) -> QueryMut<'_, Q> {
        QueryMut::new(&self.entities.meta, &mut self.archetypes.archetypes)
    }

    pub(crate) fn memo(&self) -> (u64, u32) {
        (self.id, self.archetypes.generation())
    }

    pub(crate) fn entities_meta(&self) -> &[EntityMeta] {
        &self.entities.meta
    }

    pub(crate) fn entities(&self) -> &Entities {
        &self.entities
    }

    pub(crate) fn archetypes_inner(&self) -> &sharedvec::SharedVec<Archetype> {
        &self.archetypes.archetypes
    }

    pub(crate) fn world_slot(&self) -> NonZeroU32 {
        self.world_slot
    }

    /// Resolve a GCPtr (from a CRef) to the Entity it belongs to.
    ///
    /// Returns `None` if the pointer belongs to a different world or the slot
    /// is not alive.
    ///
    /// # Safety
    /// `ptr` must be a valid GCPtr originating from this World.
    pub unsafe fn entity_from_gc_ptr(&self, ptr: crate::gc::GCPtr) -> Option<Entity> {
        if ptr.world_slot() != self.world_slot {
            return None;
        }
        let resolved = ptr.resolve_moved();
        let header = resolved.header_ptr().as_ref();
        if !matches!(header.state, crate::gc::State::Alive { .. }) {
            return None;
        }
        let entity = resolved.entity();
        if entity.id == u32::MAX {
            return None;
        }
        Some(entity)
    }

    /// Prepare a query against a single entity, using dynamic borrow checking
    ///
    /// Prefer [`query_one_mut`](Self::query_one_mut) when concurrent access to the [`World`] is not
    /// required.
    ///
    /// Call [`get`](QueryOne::get) on the resulting [`QueryOne`] to actually execute the query. The
    /// [`QueryOne`] value is responsible for releasing the dynamically-checked borrow made by
    /// `get`, so it can't be dropped while references returned by `get` are live.
    ///
    /// Handy for accessing multiple components simultaneously.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, true, "abc".to_string()));
    /// // The returned query must outlive the borrow made by `get`
    /// let mut query = world.query_one::<(&mut i32, &bool)>(a).unwrap();
    /// let (number, flag) = query.get().unwrap();
    /// if *flag { *number *= 2; }
    /// assert_eq!(*number, 246);
    /// ```
    pub fn query_one<Q: Query>(&self, entity: Entity) -> Result<QueryOne<'_, Q>, NoSuchEntity> {
        let loc = self.entities.get(entity)?;
        Ok(unsafe { QueryOne::new(&self.archetypes.archetypes[loc.archetype], loc.index) })
    }

    /// Query a single entity in a uniquely borrow world
    ///
    /// Like [`query_one`](Self::query_one), but faster because dynamic borrow checks can be
    /// skipped. Note that, unlike [`query_one`](Self::query_one), on success this returns the
    /// query's results directly.
    pub fn query_one_mut<Q: Query>(
        &mut self,
        entity: Entity,
    ) -> Result<QueryItem<'_, Q>, QueryOneError> {
        let loc = self.entities.get(entity)?;
        let archetype = &self.archetypes.archetypes[loc.archetype];
        let state = Q::Fetch::prepare(archetype).ok_or(QueryOneError::Unsatisfied)?;
        let fetch = Q::Fetch::execute(archetype, state);
        unsafe { Ok(fetch.get(loc.index as usize)) }
    }

    /// Short-hand for [`entity`](Self::entity) followed by [`EntityRef::get`]
    pub fn get<'a, T: ComponentRef<'a>>(
        &'a self,
        entity: Entity,
    ) -> Result<T::Ref, ComponentError> {
        Ok(self
            .entity(entity)?
            .get::<T>()
            .ok_or_else(MissingComponent::new::<T::Component>)?)
    }

    pub fn new_cref<'a, T: Component + 'static>(
        &'a self,
        entity: Entity,
    ) -> Result<CRef<T>, ComponentError> {
        let entity = self.entity(entity)?;
        let ptr = unsafe {
            entity
                .archetype()
                .get_dynamic(&TypeInfo::of::<T>(), entity.index())
        };
        let ptr = ptr.ok_or(ComponentError::MissingComponent(
            MissingComponent::new::<T>(),
        ))?;
        Ok(CRef {
            ptr,
            _marker: core::marker::PhantomData::default(),
        })
    }

    /// Get a raw GC pointer to `entity`'s component identified by `type_id`.
    ///
    /// Unlike `new_cref`, this takes a `StableTypeId` directly — useful for
    /// type-erased access from dynamically loaded modules.
    pub fn get_gc_ptr_by_id(
        &self,
        entity: Entity,
        type_id: crate::StableTypeId,
    ) -> Result<crate::gc::GCPtr, ComponentError> {
        let entity = self.entity(entity)?;
        let ptr = unsafe {
            entity
                .archetype()
                .get_dynamic_by_id(type_id, entity.index())
        };
        ptr.ok_or(ComponentError::MissingComponent(MissingComponent::custom(
            "<unknown component>",
        )))
    }

    /// Short-hand for [`entity`](Self::entity) followed by [`EntityRef::satisfies`]
    pub fn satisfies<Q: Query>(&self, entity: Entity) -> Result<bool, NoSuchEntity> {
        Ok(self.entity(entity)?.satisfies::<Q>())
    }

    /// Access an entity regardless of its component types
    ///
    /// Does not immediately borrow any component.
    pub fn entity(&self, entity: Entity) -> Result<EntityRef<'_>, NoSuchEntity> {
        let loc = self.entities.get(entity)?;
        unsafe {
            Ok(EntityRef::new(
                &self.archetypes.archetypes[loc.archetype],
                entity,
                loc.index,
            ))
        }
    }

    /// Given an id obtained from [`Entity::id`], reconstruct the still-live [`Entity`].
    ///
    /// # Safety
    ///
    /// `id` must correspond to a currently live [`Entity`]. A despawned or never-allocated `id`
    /// will produce undefined behavior.
    pub unsafe fn find_entity_from_id(&self, id: u32) -> Entity {
        self.entities.resolve_unknown_gen(id)
    }

    /// Iterate over all entities in the world
    ///
    /// Entities are yielded in arbitrary order. Prefer [`query`](Self::query) for better
    /// performance when components will be accessed in predictable patterns.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn(());
    /// let b = world.spawn(());
    /// let ids = world.iter().map(|entity_ref| entity_ref.entity()).collect::<Vec<_>>();
    /// assert_eq!(ids.len(), 2);
    /// assert!(ids.contains(&a));
    /// assert!(ids.contains(&b));
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter::new(&self.archetypes.archetypes, &self.entities)
    }

    /// Add `components` to `entity`
    ///
    /// Computational cost is proportional to the number of components `entity` has. If an entity
    /// already has a component of a certain type, it is dropped and replaced.
    ///
    /// When inserting a single component, see [`insert_one`](Self::insert_one) for convenience.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let e = world.spawn((123, "abc".to_string()));
    /// world.insert(e, (456, true));
    /// assert_eq!(*world.get::<&i32>(e).unwrap(), 456);
    /// assert_eq!(*world.get::<&bool>(e).unwrap(), true);
    /// ```
    pub fn insert(
        &mut self,
        entity: Entity,
        components: impl DynamicBundle,
    ) -> Result<(), NoSuchEntity> {
        self.flush();

        let loc = self.entities.get(entity)?;
        // SAFETY: we have &mut self
        unsafe { self.insert_inner_nonsync(entity, components, loc.archetype, loc) };
        Ok(())
    }

    pub unsafe fn insert_nonsync(
        &self,
        entity: Entity,
        components: impl DynamicBundle,
    ) -> Result<(), NoSuchEntity> {
        self.flush_nonsync();

        let loc = self.entities.get(entity)?;
        // SAFETY: we have are in !Sync context
        unsafe { self.insert_inner_nonsync(entity, components, loc.archetype, loc) };
        Ok(())
    }

    /// The implementation backing [`insert`](Self::insert) exposed so that it can also be used by [`exchange`](Self::exchange).
    ///
    /// Note that `graph_origin` is always equal to `loc.archetype` during insertion. Only for exchange, `graph_origin` identifies
    /// the intermediate archetype which would be reached after removal and before insertion even though
    /// the actual component data still resides in `loc.archetype`.
    unsafe fn insert_inner_nonsync(
        &self,
        entity: Entity,
        components: impl DynamicBundle,
        graph_origin: sharedvec::DefaultKey,
        loc: Location,
    ) {
        let target_storage;
        let target = match components.key() {
            None => {
                target_storage = self
                    .archetypes
                    .get_insert_target_nonsync(graph_origin, &components);
                &target_storage
            }
            Some(key) => {
                let insert_edges = self.insert_edges.0.get().as_mut().unwrap();
                match insert_edges.entry((graph_origin, key)) {
                    Entry::Occupied(entry) => entry.into_mut(),
                    Entry::Vacant(entry) => {
                        let target = self
                            .archetypes
                            .get_insert_target_nonsync(graph_origin, &components);
                        entry.insert(target)
                    }
                }
            }
        };

        let source_arch = &self.archetypes.archetypes[loc.archetype];
        unsafe {
            // Drop the components we're overwriting
            for ty in &target.replaced {
                let mut ptr = source_arch.get_dynamic(ty, loc.index).unwrap();
                ptr.drop_value_and_tombstone(&ty);
            }

            if target.index == loc.archetype {
                // Update components in the current archetype
                let arch = &self.archetypes.archetypes[loc.archetype];
                components.put(|ptr, ty| {
                    // SAFETY: we have &mut self
                    arch.put_new_dynamic_nonsync(ptr, &ty, loc.index);
                });
                return;
            }

            let source_arch = &self.archetypes.archetypes[loc.archetype];
            let target_arch = &self.archetypes.archetypes[target.index];

            // Allocate storage in the archetype and update the entity's location to address it
            let target_index = target_arch.allocate_nonsync(entity, self.world_slot);
            self.entities.meta.set_nonsync(
                entity.id as usize,
                EntityMeta {
                    generation: entity.generation,
                    location: Location {
                        archetype: target.index,
                        index: target_index,
                    },
                },
            );

            // Move the new components
            components.put(|ptr, ty| {
                target_arch.put_new_dynamic_nonsync(ptr, &ty, target_index);
            });

            // Move the components we're keeping
            for ty in &target.retained {
                let src = source_arch.get_dynamic(ty, loc.index).unwrap();
                target_arch.move_from_nonsync(src, ty, target_index);
            }
            source_arch.set_entity_free_nonsync(loc.index as usize);
        }
    }

    /// Add `component` to `entity`
    ///
    /// See [`insert`](Self::insert).
    pub fn insert_one(
        &mut self,
        entity: Entity,
        component: impl Component,
    ) -> Result<(), NoSuchEntity> {
        self.insert(entity, (component,))
    }

    /// Remove components from `entity`
    ///
    /// Computational cost is proportional to the number of components `entity` has. The entity
    /// itself is not removed, even if no components remain; use `despawn` for that. If any
    /// component in `T` is not present in `entity`, no components are removed and an error is
    /// returned.
    ///
    /// When removing a single component, see [`remove_one`](Self::remove_one) for convenience.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let e = world.spawn((123, "abc".to_string(), true));
    /// assert_eq!(world.remove::<(i32, String)>(e), Ok((123, "abc".to_string())));
    /// assert!(world.get::<&i32>(e).is_err());
    /// assert!(world.get::<&String>(e).is_err());
    /// assert_eq!(*world.get::<&bool>(e).unwrap(), true);
    /// ```
    pub fn remove<T: Bundle + 'static>(&mut self, entity: Entity) -> Result<T, ComponentError> {
        self.flush();

        // Gather current metadata
        let loc = self.entities.get_mut(entity)?;
        let old_index = loc.index;
        let source_arch = &self.archetypes.archetypes[loc.archetype];

        // Move out of the source archetype, or bail out if a component is missing
        let bundle = unsafe {
            T::get(|ty| {
                // SAFETY: We have &mut self
                let gc_ptr = source_arch.get_dynamic(&ty, old_index);
                if let Some(mut gc_ptr) = gc_ptr {
                    gc_ptr.mark_tombstone();
                }
                gc_ptr.map(|p| p.value_ptr())
            })?
        };

        // Find the target archetype ID
        let target = Self::remove_target::<T>(
            &mut self.archetypes,
            self.remove_edges.0.get_mut(),
            loc.archetype,
        );

        // Store components to the target archetype and update metadata
        if loc.archetype != target {
            // If we actually removed any components, the entity needs to be moved into a new archetype
            let source_arch = &self.archetypes.archetypes[loc.archetype];
            let target_arch = &self.archetypes.archetypes[target];
            // SAFETY: We have &mut self
            let target_index = unsafe { target_arch.allocate_nonsync(entity, self.world_slot) };
            loc.archetype = target;
            loc.index = target_index;
            if let Some(moved) = unsafe {
                source_arch.move_to(old_index, |src, ty| {
                    // Only move the components present in the target archetype, i.e. the non-removed ones.
                    if let Some(mut dst) = target_arch.get_dynamic(ty, target_index) {
                        dst.move_from(ty, src);
                    }
                })
            } {
                self.entities.meta[moved as usize].location.index = old_index;
            }
        }

        Ok(bundle)
    }

    pub unsafe fn remove_nonsync<T: Bundle + 'static>(
        &self,
        entity: Entity,
    ) -> Result<T, ComponentError> {
        self.flush_nonsync();

        let loc = self.entities.get(entity)?;
        let source_arch = &self.archetypes.archetypes[loc.archetype];

        // Extract values + mark tombstone (caller takes ownership, so no drop)
        let bundle = unsafe {
            T::get(|ty| {
                let gc_ptr = source_arch.get_dynamic(&ty, loc.index);
                if let Some(mut gc_ptr) = gc_ptr {
                    gc_ptr.mark_tombstone();
                }
                gc_ptr.map(|p| p.value_ptr())
            })?
        };

        let removed_ids =
            T::with_static_type_info(|info| info.iter().map(|t| t.id()).collect::<Vec<_>>());

        self.migrate_remove_nonsync(entity, loc, &removed_ids);
        Ok(bundle)
    }

    /// Remove components identified by `StableTypeId`s from `entity`.
    ///
    /// Drops removed values and migrates the entity to a smaller archetype.
    pub unsafe fn remove_by_ids_nonsync(
        &self,
        entity: Entity,
        type_ids: &[crate::StableTypeId],
    ) -> Result<(), ComponentError> {
        self.flush_nonsync();

        let loc = self.entities.get(entity)?;
        let source_arch = &self.archetypes.archetypes[loc.archetype];

        // Drop values and tombstone the removed components
        for &id in type_ids {
            let ty = source_arch
                .types()
                .iter()
                .find(|t| t.id() == id)
                .ok_or_else(|| {
                    ComponentError::MissingComponent(MissingComponent::custom(
                        "unknown (by StableTypeId)",
                    ))
                })?;
            let mut gc_ptr = source_arch.get_dynamic_by_id(id, loc.index).unwrap();
            gc_ptr.drop_value_and_tombstone(ty);
        }

        self.migrate_remove_nonsync(entity, loc, type_ids);
        Ok(())
    }

    /// Migrate entity to archetype without the given component types.
    ///
    /// Caller must have already tombstoned/dropped the removed components.
    unsafe fn migrate_remove_nonsync(
        &self,
        entity: Entity,
        loc: Location,
        removed_ids: &[crate::StableTypeId],
    ) {
        let source_arch = &self.archetypes.archetypes[loc.archetype];
        let info: Vec<TypeInfo> = source_arch
            .types()
            .iter()
            .filter(|x| !removed_ids.contains(&x.id()))
            .cloned()
            .collect();
        let elements = info.iter().map(|x| x.id()).collect::<Box<_>>();
        let target = self.archetypes.get_nonsync(&*elements, move || info);

        if loc.archetype != target {
            let source_arch = &self.archetypes.archetypes[loc.archetype];
            let target_arch = &self.archetypes.archetypes[target];
            let target_index = target_arch.allocate_nonsync(entity, self.world_slot);
            self.entities.meta.set_nonsync(
                entity.id as usize,
                EntityMeta {
                    location: Location {
                        archetype: target,
                        index: target_index,
                    },
                    generation: entity.generation,
                },
            );

            if let Some(moved) = source_arch.move_to(loc.index, |src, ty| {
                if !removed_ids.contains(&ty.id()) {
                    if let Some(mut dst) = target_arch.get_dynamic(ty, target_index) {
                        dst.move_from(ty, src);
                    }
                }
            }) {
                let mut old_moved = self.entities.meta[moved as usize];
                old_moved.location.index = loc.index;
                self.entities.meta.set_nonsync(moved as usize, old_moved);
            }
        }
    }

    fn remove_target<T: Bundle + 'static>(
        archetypes: &mut ArchetypeSet,
        remove_edges: &mut IndexTypeIdMap<sharedvec::DefaultKey>,
        old_archetype: sharedvec::DefaultKey,
    ) -> sharedvec::DefaultKey {
        match remove_edges.entry((old_archetype, TypeId::of::<T>())) {
            Entry::Occupied(entry) => *entry.into_mut(),
            Entry::Vacant(entry) => {
                let info = T::with_static_type_info(|removed| {
                    archetypes.archetypes[old_archetype]
                        .types()
                        .iter()
                        .filter(|x| removed.binary_search(x).is_err())
                        .cloned()
                        .collect::<Vec<_>>()
                });
                let elements = info.iter().map(|x| x.id()).collect::<Box<_>>();
                let index = archetypes.get(&*elements, move || info);
                *entry.insert(index)
            }
        }
    }

    /// Remove the `T` component from `entity`
    ///
    /// See [`remove`](Self::remove).
    pub fn remove_one<T: Component>(&mut self, entity: Entity) -> Result<T, ComponentError> {
        self.remove::<(T,)>(entity).map(|(x,)| x)
    }
    pub fn remove_one_nonsync<T: Component>(&self, entity: Entity) -> Result<T, ComponentError> {
        unsafe { self.remove_nonsync::<(T,)>(entity).map(|(x,)| x) }
    }

    /// Remove `S` components from `entity` and then add `components`
    ///
    /// This has the same effect as calling [`remove::<S>`](Self::remove) and then [`insert::<T>`](Self::insert),
    /// but is more efficient as the intermediate archetype after removal but before insertion is skipped.
    // pub fn exchange<S: Bundle + 'static, T: DynamicBundle>(
    //     &mut self,
    //     entity: Entity,
    //     components: T,
    // ) -> Result<S, ComponentError> {
    //     self.flush();

    //     // Gather current metadata
    //     let loc = self.entities.get(entity)?;

    //     // Move out of the source archetype, or bail out if a component is missing
    //     let source_arch = &self.archetypes.archetypes[loc.archetype as usize];

    //     let bundle = unsafe {
    //         S::get(|ty| {
    //             source_arch
    //                 .get_dynamic(&ty, loc.index)
    //                 .map(|p| p.value_ptr())
    //         })?
    //     };

    //     // Find the intermediate archetype ID
    //     let intermediate =
    //         Self::remove_target::<S>(&mut self.archetypes, &mut self.remove_edges, loc.archetype);

    //     self.insert_inner(entity, components, intermediate, loc);

    //     Ok(bundle)
    // }

    // /// Remove the `S` component from `entity` and then add `component`
    // ///
    // /// See [`exchange`](Self::exchange).
    // pub fn exchange_one<S: Component, T: Component>(
    //     &mut self,
    //     entity: Entity,
    //     component: T,
    // ) -> Result<S, ComponentError> {
    //     self.exchange::<(S,), (T,)>(entity, (component,))
    //         .map(|(x,)| x)
    // }

    /// Borrow a single component of `entity` without safety checks
    ///
    /// `T` must be a shared or unique reference to a component type.
    ///
    /// Should only be used as a building block for safe abstractions.
    ///
    /// # Safety
    ///
    /// `entity` must have been previously obtained from this [`World`], and no unique borrow of the
    /// same component of `entity` may be live simultaneous to the returned reference.
    pub unsafe fn get_unchecked<'a, T: ComponentRef<'a>>(
        &'a self,
        entity: Entity,
    ) -> Result<T, ComponentError> {
        let loc = self.entities.get(entity)?;
        let archetype = &self.archetypes.archetypes[loc.archetype];
        let state = archetype
            .get_state::<T::Component>()
            .ok_or_else(MissingComponent::new::<T::Component>)?;
        Ok(T::from_raw(
            archetype
                .get_data_storage(state)
                .get_value(loc.index)
                .cast()
                .as_ptr(),
        ))
    }

    /// Convert all reserved entities into empty entities that can be iterated and accessed
    ///
    /// Invoked implicitly by operations that add or remove components or entities, i.e. all
    /// variations of `spawn`, `despawn`, `insert`, and `remove`.
    pub fn flush(&mut self) {
        let arch =
            &self.archetypes.archetypes[self.archetypes.archetypes.key_from_index(0).unwrap()];
        let world_slot = self.world_slot;

        self.entities.flush(|entity, location| {
            //SAFETY: we have &mut self
            location.index = unsafe { arch.allocate_nonsync(entity, world_slot) }
        });
    }

    pub unsafe fn flush_nonsync(&self) {
        let arch =
            &self.archetypes.archetypes[self.archetypes.archetypes.key_from_index(0).unwrap()];
        let world_slot = self.world_slot;

        self.entities.flush_nonsync(|entity, location| {
            //SAFETY: we have &mut self
            location.index = unsafe { arch.allocate_nonsync(entity, world_slot) }
        });
    }

    /// Dynamically query all entities that have every component in `type_ids`.
    ///
    /// For each matching entity the callback receives the `Entity` handle and a
    /// slice of `GCPtr`s in the same order as `type_ids`.
    pub fn query_dynamic(
        &self,
        type_ids: &[crate::StableTypeId],
        cb: &mut dyn FnMut(Entity, &[crate::gc::GCPtr]),
    ) {
        // Stack-allocate for the common case (≤8 components), spill to heap otherwise
        let n = type_ids.len();
        let mut ptrs_inline = [crate::gc::GCPtr {
            value: core::ptr::NonNull::dangling(),
        }; 8];
        let mut cols_inline = [0usize; 8];
        let mut ptrs_heap;
        let mut cols_heap;
        let (ptrs, cols): (&mut [crate::gc::GCPtr], &mut [usize]) = if n <= 8 {
            (&mut ptrs_inline[..n], &mut cols_inline[..n])
        } else {
            ptrs_heap = vec![
                crate::gc::GCPtr {
                    value: core::ptr::NonNull::dangling()
                };
                n
            ];
            cols_heap = vec![0usize; n];
            (&mut ptrs_heap, &mut cols_heap)
        };
        for (_, archetype) in self.archetypes() {
            // Resolve column indices once per archetype
            let mut matched = true;
            for (i, id) in type_ids.iter().enumerate() {
                match archetype.column_index(*id) {
                    Some(col) => cols[i] = col,
                    None => {
                        matched = false;
                        break;
                    }
                }
            }
            if !matched {
                continue;
            }
            let total = archetype.allocated_values_sync();
            let entities = archetype.entities_slice();
            // Precompute strides per column
            let mut strides_inline = [0usize; 8];
            let mut strides_heap;
            let strides: &[usize] = if n <= 8 {
                for (i, &col) in cols.iter().enumerate() {
                    strides_inline[i] = unsafe { archetype.get_data_storage(col) }.stride();
                }
                &strides_inline[..n]
            } else {
                strides_heap = cols
                    .iter()
                    .map(|&col| unsafe { archetype.get_data_storage(col) }.stride())
                    .collect::<Vec<_>>();
                &strides_heap
            };
            // Iterate chunk-linearly to avoid div/mod per entity
            let epc = unsafe { archetype.get_data_storage(cols[0]) }.entities_per_chunk();
            let mut slot = 0u32;
            while slot < total {
                let chunk_idx = slot as usize / epc;
                let value_in_chunk = slot as usize % epc;
                // Set up pointers to start of this chunk run
                for (i, &col) in cols.iter().enumerate() {
                    let data = unsafe { archetype.get_data_storage(col) };
                    let chunk_base = unsafe { *data.chunks().get_unchecked(chunk_idx) };
                    let base =
                        unsafe { chunk_base.add(data.data_start() + value_in_chunk * strides[i]) };
                    ptrs[i] = unsafe {
                        crate::gc::GCPtr::from_base_with_offset(
                            data.value_start(),
                            core::ptr::NonNull::new_unchecked(base),
                        )
                    };
                }
                let run_end = (((chunk_idx + 1) * epc) as u32).min(total);
                // Linear scan: bump pointers by stride instead of recomputing
                for s in slot..run_end {
                    let entity = unsafe { entities[s as usize].read_nonsync() };
                    if entity.id != u32::MAX {
                        cb(entity, ptrs);
                    }
                    // Bump all column pointers by their stride
                    for i in 0..n {
                        ptrs[i] = crate::gc::GCPtr {
                            value: unsafe {
                                core::ptr::NonNull::new_unchecked(
                                    ptrs[i].value.as_ptr().add(strides[i]),
                                )
                            },
                        };
                    }
                }
                slot = run_end;
            }
        }
    }

    /// Like `query_dynamic`, but skips entity resolution — only passes component pointers.
    pub fn query_dynamic_values(
        &self,
        type_ids: &[crate::StableTypeId],
        cb: &mut dyn FnMut(&[crate::gc::GCPtr]),
    ) {
        let n = type_ids.len();
        let mut ptrs_inline = [crate::gc::GCPtr {
            value: core::ptr::NonNull::dangling(),
        }; 8];
        let mut cols_inline = [0usize; 8];
        let mut ptrs_heap;
        let mut cols_heap;
        let (ptrs, cols): (&mut [crate::gc::GCPtr], &mut [usize]) = if n <= 8 {
            (&mut ptrs_inline[..n], &mut cols_inline[..n])
        } else {
            ptrs_heap = vec![
                crate::gc::GCPtr {
                    value: core::ptr::NonNull::dangling()
                };
                n
            ];
            cols_heap = vec![0usize; n];
            (&mut ptrs_heap, &mut cols_heap)
        };
        for (_, archetype) in self.archetypes() {
            let mut matched = true;
            for (i, id) in type_ids.iter().enumerate() {
                match archetype.column_index(*id) {
                    Some(col) => cols[i] = col,
                    None => {
                        matched = false;
                        break;
                    }
                }
            }
            if !matched {
                continue;
            }
            let total = archetype.allocated_values_sync();
            let entities = archetype.entities_slice();
            let mut strides_inline = [0usize; 8];
            let mut strides_heap;
            let strides: &[usize] = if n <= 8 {
                for (i, &col) in cols.iter().enumerate() {
                    strides_inline[i] = unsafe { archetype.get_data_storage(col) }.stride();
                }
                &strides_inline[..n]
            } else {
                strides_heap = cols
                    .iter()
                    .map(|&col| unsafe { archetype.get_data_storage(col) }.stride())
                    .collect::<Vec<_>>();
                &strides_heap
            };
            let epc = unsafe { archetype.get_data_storage(cols[0]) }.entities_per_chunk();
            let mut slot = 0u32;
            while slot < total {
                let chunk_idx = slot as usize / epc;
                let value_in_chunk = slot as usize % epc;
                for (i, &col) in cols.iter().enumerate() {
                    let data = unsafe { archetype.get_data_storage(col) };
                    let chunk_base = unsafe { *data.chunks().get_unchecked(chunk_idx) };
                    let base =
                        unsafe { chunk_base.add(data.data_start() + value_in_chunk * strides[i]) };
                    ptrs[i] = unsafe {
                        crate::gc::GCPtr::from_base_with_offset(
                            data.value_start(),
                            core::ptr::NonNull::new_unchecked(base),
                        )
                    };
                }
                let run_end = (((chunk_idx + 1) * epc) as u32).min(total);
                for s in slot..run_end {
                    let entity_id = unsafe { entities[s as usize].read_id_nonsync() };
                    if entity_id != u32::MAX {
                        cb(ptrs);
                    }
                    for i in 0..n {
                        ptrs[i] = crate::gc::GCPtr {
                            value: unsafe {
                                core::ptr::NonNull::new_unchecked(
                                    ptrs[i].value.as_ptr().add(strides[i]),
                                )
                            },
                        };
                    }
                }
                slot = run_end;
            }
        }
    }

    /// Inspect the archetypes that entities are organized into
    ///
    /// Useful for dynamically scheduling concurrent queries by checking borrows in advance, and for
    /// efficient serialization.
    pub fn archetypes(&self) -> impl Iterator<Item = (sharedvec::DefaultKey, &'_ Archetype)> + '_ {
        self.archetypes_inner().iter()
    }

    /// Despawn `entity`, yielding a [`DynamicBundle`] of its components
    ///
    /// Useful for moving entities between worlds.
    pub fn take(&mut self, entity: Entity) -> Result<TakenEntity<'_>, NoSuchEntity> {
        self.flush();
        let loc = self.entities.get(entity)?;
        let archetype = &mut self.archetypes.archetypes[loc.archetype];
        unsafe {
            Ok(TakenEntity::new(
                &mut self.entities,
                entity,
                archetype,
                loc.index,
            ))
        }
    }

    /// Returns a distinct value after `archetypes` is changed
    ///
    /// Store the current value after deriving information from [`archetypes`](Self::archetypes),
    /// then check whether the value returned by this function differs before attempting an
    /// operation that relies on its correctness. Useful for determining whether e.g. a concurrent
    /// query execution plan is still correct.
    ///
    /// The generation may be, but is not necessarily, changed as a result of adding or removing any
    /// entity or component.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let initial_gen = world.archetypes_generation();
    /// world.spawn((123, "abc".to_string()));
    /// assert_ne!(initial_gen, world.archetypes_generation());
    /// ```
    pub fn archetypes_generation(&self) -> ArchetypesGeneration {
        ArchetypesGeneration(self.archetypes.generation())
    }

    /// Number of currently live entities
    #[inline]
    pub fn len(&self) -> u32 {
        self.entities.len()
    }

    /// Whether no entities are live
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// unsafe impl Send for World {}
// unsafe impl Sync for World {}

impl Default for World {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> IntoIterator for &'a World {
    type IntoIter = Iter<'a>;
    type Item = EntityRef<'a>;
    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

fn index2<T>(x: &mut [T], i: usize, j: usize) -> (&mut T, &mut T) {
    assert!(i != j);
    assert!(i < x.len());
    assert!(j < x.len());
    let ptr = x.as_mut_ptr();
    unsafe { (&mut *ptr.add(i), &mut *ptr.add(j)) }
}
fn index2_nonsync<T>(x: &[T], i: usize, j: usize) -> (&T, &T) {
    assert!(i != j);
    assert!(i < x.len());
    assert!(j < x.len());
    let ptr = x.as_ptr();
    unsafe { (&*ptr.add(i), &*ptr.add(j)) }
}

/// Errors that arise when accessing components
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ComponentError {
    /// The entity was already despawned
    NoSuchEntity,
    /// The entity did not have a requested component
    MissingComponent(MissingComponent),
}

#[cfg(feature = "std")]
impl Error for ComponentError {}

impl fmt::Display for ComponentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ComponentError::*;
        match *self {
            NoSuchEntity => f.write_str("no such entity"),
            MissingComponent(ref x) => x.fmt(f),
        }
    }
}

impl From<NoSuchEntity> for ComponentError {
    fn from(NoSuchEntity: NoSuchEntity) -> Self {
        ComponentError::NoSuchEntity
    }
}

impl From<MissingComponent> for ComponentError {
    fn from(x: MissingComponent) -> Self {
        ComponentError::MissingComponent(x)
    }
}

/// Errors that arise when querying a single entity
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum QueryOneError {
    /// The entity was already despawned
    NoSuchEntity,
    /// The entity exists but does not satisfy the query
    Unsatisfied,
}

#[cfg(feature = "std")]
impl Error for QueryOneError {}

impl fmt::Display for QueryOneError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use QueryOneError::*;
        match *self {
            NoSuchEntity => f.write_str("no such entity"),
            Unsatisfied => f.write_str("unsatisfied"),
        }
    }
}

impl From<NoSuchEntity> for QueryOneError {
    fn from(NoSuchEntity: NoSuchEntity) -> Self {
        QueryOneError::NoSuchEntity
    }
}

/// Types that can be components.
///
/// Requires `Send + Sync + 'static` and a `STABLE_TYPE_ID` — a cross-cdylib
/// stable type identifier computed from the type's qualified name.
///
/// Use `#[derive(Component)]` to implement this trait. Common std types
/// (primitives, String, etc.) have built-in impls.
pub trait Component: Send + Sync + 'static {
    /// A stable type identifier computed at compile time from the type's
    /// qualified name. Unlike `std::any::TypeId`, this is identical across
    /// separately compiled cdylibs that share the same source crate.
    const STABLE_TYPE_ID: crate::StableTypeId;

    /// The qualified type name used to compute STABLE_TYPE_ID.
    /// Matches `concat!(module_path!(), "::", stringify!(Type))`.
    const TYPE_NAME: &'static str = "<unknown>";
}

/// Implement `Component` for a type using `module_path!() :: stringify!()` as
/// the hash input. For use on types defined in hecs or std.
macro_rules! impl_component {
    ($($ty:ty),* $(,)?) => {
        $(
            impl Component for $ty {
                const STABLE_TYPE_ID: crate::StableTypeId = crate::StableTypeId(
                    crate::StableTypeId::fnv1a(
                        concat!(module_path!(), "::", stringify!($ty)).as_bytes()
                    )
                );
                const TYPE_NAME: &'static str = concat!(module_path!(), "::", stringify!($ty));
            }
        )*
    };
}

// Primitives and common std types
impl_component!(
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    f32,
    f64,
    bool,
    char,
    (),
);
impl_component!(alloc::string::String);
impl_component!(alloc::vec::Vec<u8>);

impl Component for alloc::borrow::Cow<'static, str> {
    const STABLE_TYPE_ID: crate::StableTypeId = crate::StableTypeId(crate::StableTypeId::fnv1a(
        b"alloc::borrow::Cow<'static, str>",
    ));
    const TYPE_NAME: &'static str = "alloc::borrow::Cow<'static, str>";
}

/// Implement `Component` for `[T; N]` arrays of common sizes.
macro_rules! impl_component_array {
    ($($n:literal),* $(,)?) => {
        $(
            impl<T: Component> Component for [T; $n] {
                const STABLE_TYPE_ID: crate::StableTypeId = crate::StableTypeId(
                    T::STABLE_TYPE_ID.0 ^ crate::StableTypeId::fnv1a(
                        concat!("[; ", stringify!($n), "]").as_bytes()
                    )
                );
            }
        )*
    };
}
impl_component_array!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 24, 32, 48, 64, 128, 256, 512, 1024,
    2048, 4096,
);

/// Iterator over all of a world's entities
pub struct Iter<'a> {
    archetypes: sharedvec::Iter<'a, Archetype, sharedvec::DefaultKey>,
    entities: &'a Entities,
    current: Option<&'a Archetype>,
    index: u32,
}

impl<'a> Iter<'a> {
    fn new(archetypes: &'a sharedvec::SharedVec<Archetype>, entities: &'a Entities) -> Self {
        Self {
            archetypes: archetypes.iter(),
            entities,
            current: None,
            index: 0,
        }
    }
}

unsafe impl Send for Iter<'_> {}
unsafe impl Sync for Iter<'_> {}

impl<'a> Iterator for Iter<'a> {
    type Item = EntityRef<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.current {
                None => {
                    self.current = Some(self.archetypes.next()?.1);
                    self.index = 0;
                }
                Some(current) => {
                    if self.index == current.allocated_values_sync() {
                        self.current = None;
                        continue;
                    }
                    let index = self.index;
                    self.index += 1;
                    let entity = current.entity(index);
                    if entity.id == u32::MAX {
                        continue;
                    }
                    return Some(unsafe { EntityRef::new(current, entity, index) });
                }
            }
        }
    }
}

impl<A: DynamicBundle> Extend<A> for World {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = A>,
    {
        for x in iter {
            self.spawn(x);
        }
    }
}

impl<A: DynamicBundle> core::iter::FromIterator<A> for World {
    fn from_iter<I: IntoIterator<Item = A>>(iter: I) -> Self {
        let mut world = World::new();
        world.extend(iter);
        world
    }
}

/// Determines freshness of information derived from [`World::archetypes`]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ArchetypesGeneration(u32);

/// Entity IDs created by [`World::spawn_batch`]
pub struct SpawnBatchIter<'a, I>
where
    I: Iterator,
    I::Item: Bundle,
{
    inner: I,
    entities: &'a mut Entities,
    archetype_id: sharedvec::DefaultKey,
    archetype: &'a mut Archetype,
    world_slot: &'a NonZeroU32,
}

impl<I> Drop for SpawnBatchIter<'_, I>
where
    I: Iterator,
    I::Item: Bundle,
{
    fn drop(&mut self) {
        for _ in self {}
    }
}

impl<I> Iterator for SpawnBatchIter<'_, I>
where
    I: Iterator,
    I::Item: Bundle,
{
    type Item = Entity;

    fn next(&mut self) -> Option<Entity> {
        let components = self.inner.next()?;
        let entity = self.entities.alloc();
        // SAFETY: we have &mut Archetype
        let index = unsafe { self.archetype.allocate_nonsync(entity, *self.world_slot) };
        unsafe {
            components.put(|ptr, ty| {
                // SAFETY: we have &mut Archetype
                self.archetype.put_new_dynamic_nonsync(ptr, &ty, index);
            });
        }
        self.entities.meta[entity.id as usize].location = Location {
            archetype: self.archetype_id,
            index,
        };
        Some(entity)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<I, T> ExactSizeIterator for SpawnBatchIter<'_, I>
where
    I: ExactSizeIterator<Item = T>,
    T: Bundle,
{
    fn len(&self) -> usize {
        self.inner.len()
    }
}

/// Iterator over [`Entity`]s spawned by [`World::spawn_column_batch()`]
pub struct SpawnColumnBatchIter<'a> {
    pending_end: usize,
    id_alloc: crate::entities::AllocManyState,
    entities: &'a mut Entities,
}

impl Iterator for SpawnColumnBatchIter<'_> {
    type Item = Entity;

    fn next(&mut self) -> Option<Entity> {
        let id = self.id_alloc.next(self.entities)?;
        Some(unsafe { self.entities.resolve_unknown_gen(id) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for SpawnColumnBatchIter<'_> {
    fn len(&self) -> usize {
        self.id_alloc.len(self.entities)
    }
}

impl Drop for SpawnColumnBatchIter<'_> {
    fn drop(&mut self) {
        // Consume used freelist entries
        self.entities.finish_alloc_many(self.pending_end);
    }
}

struct ArchetypeSet {
    /// Maps sorted component type sets to archetypes
    index: NonSyncCell<HashMap<Box<[crate::StableTypeId]>, sharedvec::DefaultKey>>,
    archetypes: sharedvec::SharedVec<Archetype>,
}

impl ArchetypeSet {
    fn new() -> Self {
        // `flush` assumes archetype 0 always exists, representing entities with no components.
        let default_archetype = Archetype::new(Vec::new());
        let archetypes = sharedvec::SharedVec::new();
        let (key, _) = archetypes.push(default_archetype);
        Self {
            index: NonSyncCell(UnsafeCell::new(
                Some((Box::default(), key)).into_iter().collect(),
            )),
            archetypes,
        }
    }

    /// Find the archetype ID that has exactly `components`
    fn get<T: Borrow<[crate::StableTypeId]> + Into<Box<[crate::StableTypeId]>>>(
        &mut self,
        components: T,
        info: impl FnOnce() -> Vec<TypeInfo>,
    ) -> sharedvec::DefaultKey {
        self.index
            .0
            .get_mut()
            .get(components.borrow())
            .copied()
            .unwrap_or_else(|| self.insert(components.into(), info()))
    }
    unsafe fn get_nonsync<T: Borrow<[crate::StableTypeId]> + Into<Box<[crate::StableTypeId]>>>(
        &self,
        components: T,
        info: impl FnOnce() -> Vec<TypeInfo>,
    ) -> sharedvec::DefaultKey {
        unsafe { &*self.index.0.get() }
            .get(components.borrow())
            .copied()
            .unwrap_or_else(|| self.insert_nonsync(components.into(), info()))
    }

    fn insert(
        &mut self,
        components: Box<[crate::StableTypeId]>,
        info: Vec<TypeInfo>,
    ) -> sharedvec::DefaultKey {
        let (key, _) = self.archetypes.push(Archetype::new(info));
        let idx = self.index.0.get_mut();
        let old = idx.insert(components, key);
        debug_assert!(old.is_none(), "inserted duplicate archetype");
        key
    }
    unsafe fn insert_nonsync(
        &self,
        components: Box<[crate::StableTypeId]>,
        info: Vec<TypeInfo>,
    ) -> sharedvec::DefaultKey {
        let (key, _) = self.archetypes.push(Archetype::new(info));
        let idx = unsafe { &mut *self.index.0.get() };
        let old = idx.insert(components, key);
        debug_assert!(old.is_none(), "inserted duplicate archetype");
        key
    }

    /// Returns archetype ID and starting location index
    fn insert_batch(&mut self, archetype: Archetype) -> (sharedvec::DefaultKey, u32) {
        let ids = archetype
            .types()
            .iter()
            .map(|info| info.id())
            .collect::<Box<_>>();

        let index = self.index.0.get_mut();
        match index.entry(ids) {
            Entry::Occupied(x) => {
                // Duplicate of existing archetype
                let existing = &mut self.archetypes[*x.get()];
                // SAFETY: we have &mut self
                let base = unsafe { existing.allocated_values_nonsync() };
                unsafe {
                    todo!();
                    // existing.merge(archetype, self.world_slot);
                }
                (*x.get(), base)
            }
            Entry::Vacant(x) => {
                // Brand new archetype
                let (id, _) = self.archetypes.push(archetype);
                x.insert(id);
                (id, 0)
            }
        }
    }

    fn generation(&self) -> u32 {
        self.archetypes.len() as u32
    }

    unsafe fn get_insert_target_nonsync(
        &self,
        src: sharedvec::DefaultKey,
        components: &impl DynamicBundle,
    ) -> InsertTarget {
        // Assemble Vec<TypeInfo> for the final entity
        let arch = &self.archetypes[src];
        let mut info = arch.types().to_vec();
        let mut replaced = Vec::new(); // Elements in both archetype.types() and components.type_info()
        let mut retained = Vec::new(); // Elements in archetype.types() but not components.type_info()

        // Because both `components.type_info()` and `arch.types()` are
        // ordered, we can identify elements in one but not the other efficiently with parallel
        // iteration.
        let mut src_ty = 0;
        for ty in components.type_info() {
            while src_ty < arch.types().len() && arch.types()[src_ty] <= ty {
                if arch.types()[src_ty] != ty {
                    retained.push(arch.types()[src_ty].clone());
                }
                src_ty += 1;
            }
            if arch.has_dynamic(ty.id()) {
                replaced.push(ty);
            } else {
                info.push(ty);
            }
        }
        info.sort_unstable();
        retained.extend_from_slice(&arch.types()[src_ty..]);

        // Find the archetype it'll live in
        let elements = info.iter().map(|x| x.id()).collect::<Box<_>>();
        let index = self.get_nonsync(elements, move || info);
        InsertTarget {
            replaced,
            retained,
            index,
        }
    }
}

/// Metadata cached for inserting components into entities from this archetype
struct InsertTarget {
    /// Components from the current archetype that are replaced by the insert
    replaced: Vec<TypeInfo>,
    /// Components from the current archetype that are moved by the insert
    retained: Vec<TypeInfo>,
    /// ID of the target archetype
    index: sharedvec::DefaultKey,
}

type IndexTypeIdMap<V> =
    HashMap<(sharedvec::DefaultKey, TypeId), V, BuildHasherDefault<IndexTypeIdHasher>>;

#[derive(Default)]
struct IndexTypeIdHasher(u64);

impl Hasher for IndexTypeIdHasher {
    fn write_u32(&mut self, index: u32) {
        self.0 ^= u64::from(index);
    }

    fn write_u64(&mut self, type_id: u64) {
        self.0 ^= type_id;
    }

    fn write(&mut self, _bytes: &[u8]) {
        unreachable!()
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use alloc::string::{String, ToString};

    use super::*;

    pub(crate) fn cleanup(mut world: World) {
        world.clear();
        unsafe { crate::gc::sweep(&world) };
    }
    #[test]
    fn reuse_empty() {
        let mut world = World::new();
        let a = world.spawn(());
        world.despawn(a).unwrap();
        let b = world.spawn(());
        assert_eq!(a.id, b.id);
        assert_ne!(a.generation, b.generation);
        cleanup(world);
    }

    #[test]
    fn clear_repeats_entity_id() {
        let mut world = World::new();
        let a = world.spawn(());
        world.clear();
        let b = world.spawn(());
        assert_eq!(a.id, b.id);
        assert_eq!(a.generation, b.generation);
        cleanup(world);
    }

    #[test]
    fn spawn_at() {
        let mut world = World::new();
        let a = world.spawn(());
        world.despawn(a).unwrap();
        let b = world.spawn(());
        assert!(world.contains(b));
        assert_eq!(a.id, b.id);
        assert_ne!(a.generation, b.generation);
        world.spawn_at(a, ());
        assert!(!world.contains(b));
        assert_eq!(b.id, a.id);
        assert_ne!(b.generation, a.generation);
        cleanup(world);
    }

    #[test]
    fn reuse_populated() {
        let mut world = World::new();
        let a = world.spawn((42,));
        assert_eq!(*world.get::<&i32>(a).unwrap(), 42);
        world.despawn(a).unwrap();
        let b = world.spawn((true,));
        assert_eq!(a.id, b.id);
        assert_ne!(a.generation, b.generation);
        assert!(world.get::<&i32>(b).is_err());
        assert!(*world.get::<&bool>(b).unwrap());
        cleanup(world);
    }

    #[test]
    fn remove_nothing() {
        let mut world = World::new();
        let a = world.spawn(("abc".to_string(), 123));
        world.remove::<()>(a).unwrap();
        cleanup(world);
    }

    #[test]
    fn bad_insert() {
        let mut world = World::new();
        assert!(world.insert_one(Entity::DANGLING, ()).is_err());
        cleanup(world);
    }

    #[test]
    fn remove_by_ids_nonsync_single() {
        let mut world = World::new();
        let e = world.spawn((42i32, "hello".to_string(), true));
        // Remove i32 by StableTypeId
        unsafe {
            world
                .remove_by_ids_nonsync(e, &[i32::STABLE_TYPE_ID])
                .unwrap();
        }
        // i32 is gone
        assert!(world.get::<&i32>(e).is_err());
        // String and bool remain
        assert_eq!(*world.get::<&String>(e).unwrap(), "hello");
        assert_eq!(*world.get::<&bool>(e).unwrap(), true);
        cleanup(world);
    }

    #[test]
    fn remove_by_ids_nonsync_multiple() {
        let mut world = World::new();
        let e = world.spawn((42i32, "hello".to_string(), true));
        // Remove i32 and bool in one call
        unsafe {
            world
                .remove_by_ids_nonsync(e, &[i32::STABLE_TYPE_ID, bool::STABLE_TYPE_ID])
                .unwrap();
        }
        assert!(world.get::<&i32>(e).is_err());
        assert!(world.get::<&bool>(e).is_err());
        assert_eq!(*world.get::<&String>(e).unwrap(), "hello");
        cleanup(world);
    }

    #[test]
    fn remove_by_ids_nonsync_missing_component() {
        let mut world = World::new();
        let e = world.spawn(("hello".to_string(),));
        // Removing a component the entity doesn't have should error
        let result = unsafe { world.remove_by_ids_nonsync(e, &[i32::STABLE_TYPE_ID]) };
        assert!(result.is_err());
        // Entity still has its original component
        assert_eq!(*world.get::<&String>(e).unwrap(), "hello");
        cleanup(world);
    }

    #[test]
    fn remove_by_ids_nonsync_no_such_entity() {
        let mut world = World::new();
        let result =
            unsafe { world.remove_by_ids_nonsync(Entity::DANGLING, &[i32::STABLE_TYPE_ID]) };
        assert!(result.is_err());
        cleanup(world);
    }
}
