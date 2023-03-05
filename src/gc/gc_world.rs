use core::marker::PhantomData;

use crate::{
    Bundle, CRef, Component, ComponentError, DynamicBundle, Entity, MissingComponent, NoSuchEntity,
    TypeInfo, World,
};

use super::query::{Query, QueryBorrow};

pub struct GCWorld<'a> {
    original_world_ref: &'a mut World,
    // We have to take ownership by core::mem::swap-ing the World into the scope,
    // since it'd otherwise be possible to core::mem::forget the ErgoScope to avoid
    // invoking the `Drop` impl, which is required for soundness.
    pub(super) world: World,
}

impl<'a> GCWorld<'a> {
    pub fn new(world: &'a mut World) -> Self {
        let mut world_temp = World::default();
        unsafe { super::enable_gc_borrows(world.world_slot()) };
        core::mem::swap(&mut world_temp, world);
        Self {
            original_world_ref: world,
            world: world_temp,
        }
    }

    /// Returns a `CRef` to the `T` component of `entity`
    pub fn get<T: Component>(&self, entity: Entity) -> Result<CRef<T>, ComponentError> {
        let entity_ref = self.world.entity(entity)?;
        let gc_ptr = unsafe {
            entity_ref
                .archetype()
                .get_dynamic(&TypeInfo::of::<T>(), entity_ref.index())
        };
        gc_ptr
            .map(|ptr| CRef {
                ptr,
                _marker: PhantomData::default(),
            })
            .ok_or_else(|| ComponentError::MissingComponent(MissingComponent::new::<T>()))
    }

    /// Add `component` to `entity`
    ///
    /// See [`insert`](Self::insert).
    pub fn insert_one(
        &self,
        entity: Entity,
        component: impl Component,
    ) -> Result<(), NoSuchEntity> {
        self.insert(entity, (component,))
    }

    /// Add `components` to `entity`
    ///
    /// When inserting a single component, see [`insert_one`](Self::insert_one) for convenience.
    pub fn insert(
        &self,
        entity: Entity,
        components: impl DynamicBundle,
    ) -> Result<(), NoSuchEntity> {
        todo!()
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
    /// # use hecs::gc::*;
    /// let mut world = hecs::World::new();
    /// let ergo = GCWorld::new(&mut world);
    /// let a = ergo.spawn((123, "abc".to_string()));
    /// let b = ergo.spawn((456, true));
    /// ```
    pub fn spawn(&self, components: impl DynamicBundle) -> Entity {
        todo!();
    }

    // fn spawn_inner(&mut self, entity: Entity, components: impl DynamicBundle) {
    //     let archetype_id = match components.key() {
    //         Some(k) => {
    //             let archetypes = &mut self.archetypes;
    //             *self.bundle_to_archetype.entry(k).or_insert_with(|| {
    //                 components.with_ids(|ids| archetypes.get(ids, || components.type_info()))
    //             })
    //         }
    //         None => components.with_ids(|ids| self.archetypes.get(ids, || components.type_info())),
    //     };

    //     let archetype = &mut self.archetypes.archetypes[archetype_id as usize];
    //     unsafe {
    //         let index = archetype.allocate(entity.id, self.world_slot);
    //         components.put(|ptr, ty| {
    //             archetype.put_new_dynamic(ptr, &ty, index);
    //         });
    //         self.entities.meta[entity.id as usize].location = Location {
    //             archetype: archetype_id,
    //             index,
    //         };
    //     }
    // }

    /// Create an entity with certain components and a specific [`Entity`] handle.
    ///
    /// See [`spawn`](Self::spawn).
    ///
    /// Despawns any existing entity with the same [`Entity::id`].
    ///
    /// # Example
    /// ```
    /// # use hecs::gc::*;
    /// let mut world = hecs::World::new();
    /// let ergo = GCWorld::new(&mut world);
    /// let a = ergo.spawn((123, "abc".to_string()));
    /// let b = ergo.spawn((456, true));
    /// ergo.despawn(a);
    /// assert!(!ergo.contains(a));
    /// // all previous Entity values pointing to 'a' will be live again, instead pointing to the new entity.
    /// ergo.spawn_at(a, (789, "ABC".to_string()));
    /// assert!(ergo.contains(a));
    /// ```
    pub fn spawn_at(&self, entity: Entity, components: impl DynamicBundle) {
        todo!();
    }

    /// Allocate an entity ID
    pub fn reserve_entity(&self) -> Entity {
        self.world.entities().reserve_entity()
    }

    /// Remove the `T` component from `entity`
    ///
    /// See [`remove`](Self::remove).
    pub fn remove_one<T: Component>(&self, entity: Entity) -> Result<T, ComponentError> {
        todo!()
    }

    /// Remove components from `entity`
    ///
    /// When removing a single component, see [`remove_one`](Self::remove_one) for convenience.
    pub fn remove<T: Bundle + 'static>(&self, entity: Entity) -> Result<T, ComponentError> {
        todo!()
    }

    // /// Destroy an entity and all its components
    pub fn despawn(&self, entity: Entity) -> Result<(), NoSuchEntity> {
        todo!()
    }

    // TODO implement len()

    // TODO implement
    pub fn satisfies<Q: Query>(&self, entity: Entity) -> Result<bool, NoSuchEntity> {
        todo!()
    }

    /// Whether `entity` exists
    pub fn contains(&self, entity: Entity) -> bool {
        self.world.contains(entity)
    }

    // TODO implement query_one

    /// Iterate over all entities that have certain components.
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
    /// Iterating a query yields references with lifetimes bound to the [`QueryBorrow`] returned
    /// here. To ensure those are invalidated, the return value of this method must be dropped for
    /// its dynamic borrows from the world to be released. Similarly, lifetime rules ensure that
    /// references obtained from a query cannot outlive the [`QueryBorrow`].
    ///
    /// # Example
    /// ```
    /// # use hecs::gc::*;
    /// let mut world = hecs::World::new();
    /// let a = world.spawn((123, true, "abc".to_string()));
    /// let b = world.spawn((456, false));
    /// let c = world.spawn((42, "def".to_string()));
    /// let ergo = GCWorld::new(&mut world);
    /// let entities = ergo.query::<(&i32, &bool)>()
    ///     .iter()
    ///     .map(|(e, (i, b))| (e, *i.read(), *b.read())) // Copy out of the world
    ///     .collect::<Vec<_>>();
    /// assert_eq!(entities.len(), 2);
    /// assert!(entities.contains(&(a, 123, true)));
    /// assert!(entities.contains(&(b, 456, false)));
    /// ```
    pub fn query<Q: Query>(&self) -> QueryBorrow<'_, Q> {
        QueryBorrow::new(&self.world.entities().meta, self.world.archetypes_inner())
    }
}

impl<'a> Drop for GCWorld<'a> {
    fn drop(&mut self) {
        unsafe { super::disable_gc_borrows(self.world.world_slot()) };
        core::mem::swap(self.original_world_ref, &mut self.world);
    }
}
