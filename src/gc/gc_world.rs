use core::{
    marker::PhantomData,
    num::NonZeroU32,
    ops::{Deref, DerefMut},
};

use crate::{
    Archetype, Bundle, CRef, Component, ComponentError, DynamicBundle, Entity, MissingComponent,
    NoSuchEntity, QueryOneError, TypeInfo, World,
};

use super::query::{Fetch, Query, QueryBorrow, QueryItem};
use super::{slot_mode, SlotMode};

#[inline]
fn assert_writable(slot: NonZeroU32) {
    assert_eq!(
        slot_mode(slot),
        SlotMode::GcDynamic,
        "GcWorld mutation attempted while a ReadWorld scope is active"
    );
}

pub struct GcWorldScope<'a> {
    original_world_ref: &'a mut World,
    gc_world: GcWorld,
}
impl<'a> Deref for GcWorldScope<'a> {
    type Target = GcWorld;

    fn deref(&self) -> &Self::Target {
        &self.gc_world
    }
}
impl<'a> DerefMut for GcWorldScope<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.gc_world
    }
}

pub struct GcWorld {
    pub(super) world: World,
}

impl GcWorld {
    pub fn new() -> Self {
        let world = World::new();
        unsafe { super::enable_gc_borrows(world.world_slot()) };
        Self { world }
    }
    pub fn new_scope(world: &mut World) -> GcWorldScope<'_> {
        let mut world_temp = World::default();
        unsafe { super::enable_gc_borrows(world.world_slot()) };
        // We have to take ownership by core::mem::swap-ing the World into the scope,
        // since it'd otherwise be possible to core::mem::forget the ErgoScope to avoid
        // invoking the `Drop` impl, which is required for soundness.
        core::mem::swap(&mut world_temp, world);
        GcWorldScope {
            original_world_ref: world,
            gc_world: Self { world: world_temp },
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
        assert_writable(self.world.world_slot());
        unsafe { self.world.insert_nonsync(entity, components) }
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
    /// let ergo = GcWorld::new_scope(&mut world);
    /// let a = ergo.spawn((123, "abc".to_string()));
    /// let b = ergo.spawn((456, true));
    /// ```
    pub fn spawn(&self, components: impl DynamicBundle) -> Entity {
        assert_writable(self.world.world_slot());
        unsafe { self.world.spawn_nonsync(components) }
    }

    /// Remove the `T` component from `entity`
    ///
    /// See [`remove`](Self::remove).
    pub fn remove_one<T: Component>(&self, entity: Entity) -> Result<T, ComponentError> {
        assert_writable(self.world.world_slot());
        unsafe { self.world.remove_one_nonsync::<T>(entity) }
    }

    /// Remove components from `entity`
    ///
    /// When removing a single component, see [`remove_one`](Self::remove_one) for convenience.
    pub fn remove<T: Bundle + 'static>(&self, entity: Entity) -> Result<T, ComponentError> {
        assert_writable(self.world.world_slot());
        unsafe { self.world.remove_nonsync::<T>(entity) }
    }

    // /// Destroy an entity and all its components
    pub fn despawn(&self, entity: Entity) -> Result<(), NoSuchEntity> {
        assert_writable(self.world.world_slot());
        unsafe { self.world.despawn_nonsync(entity) }
    }

    /// Returns the number of entities in the world
    pub fn len(&self) -> u32 {
        self.world.len()
    }

    /// Returns `true` if the world contains no entities
    pub fn is_empty(&self) -> bool {
        self.world.is_empty()
    }

    /// Resolve entity location, returning `Err` if despawned (including nonsync/tombstoned)
    fn resolve(&self, entity: Entity) -> Result<(&Archetype, u32), NoSuchEntity> {
        let loc = self.world.entities().get(entity)?;
        let archetype = &self.world.archetypes_inner()[loc.archetype];
        if archetype.entity(loc.index).id == u32::MAX {
            return Err(NoSuchEntity);
        }
        Ok((archetype, loc.index))
    }

    /// Returns an [`EntityRef`] for the given entity
    pub fn entity(&self, entity: Entity) -> Result<EntityRef<'_>, NoSuchEntity> {
        let (archetype, index) = self.resolve(entity)?;
        Ok(EntityRef {
            archetype,
            entity,
            index,
        })
    }

    /// Returns `true` if `entity` satisfies the query `Q`
    pub fn satisfies<Q: Query>(&self, entity: Entity) -> Result<bool, NoSuchEntity> {
        let e = self.entity(entity)?;
        Ok(Q::Fetch::prepare(e.archetype()).is_some())
    }

    /// Whether `entity` exists
    pub fn contains(&self, entity: Entity) -> bool {
        self.resolve(entity).is_ok()
    }

    /// Query a single entity
    pub fn query_one<Q: Query>(&self, entity: Entity) -> Result<QueryItem<'_, Q>, QueryOneError> {
        let (archetype, index) = self.resolve(entity)?;
        let state = Q::Fetch::prepare(archetype).ok_or(QueryOneError::Unsatisfied)?;
        let fetch = Q::Fetch::execute(archetype, state);
        unsafe { Ok(fetch.get(index as usize)) }
    }

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
    /// let ergo = GcWorld::new_scope(&mut world);
    /// let entities = ergo.query::<(&i32, &bool)>()
    ///     .iter()
    ///     .map(|(e, (i, b))| (e, *i.read(), *b.read())) // Copy out of the world
    ///     .collect::<Vec<_>>();
    /// assert_eq!(entities.len(), 2);
    /// assert!(entities.contains(&(a, 123, true)));
    /// assert!(entities.contains(&(b, 456, false)));
    /// ```
    pub fn query<Q: Query>(&self) -> QueryBorrow<'_, Q> {
        QueryBorrow::new(
            &self.world.entities().meta,
            self.world.archetypes_inner().iter(),
        )
    }

    /// Enter a read-only scope on this world.
    ///
    /// While the returned [`ReadWorld`] is alive, all `GcWorld` mutation methods
    /// (`spawn`, `insert`, `remove`, `despawn`, ...) panic, and [`CRef::write`] panics.
    /// In exchange, [`CRef::read_bypass`] becomes available — it hands out a `&T`
    /// bound to the scope's lifetime without touching the dynamic borrow counter.
    /// [`CRef::read`] continues to work and behaves exactly as in `GcDynamic` mode
    /// (incrementing the borrow counter, returning a `Ref<'_, T>`) so any `Ref`
    /// still outstanding when the scope drops keeps `write()` blocked until it does.
    ///
    /// `ReadWorld` scopes are reentrant — open as many as you like; the slot returns
    /// to its writable state only when the last one drops.
    pub fn read_only(&self) -> ReadWorld<'_> {
        unsafe { super::enter_read_only(self.world.world_slot()) };
        ReadWorld { gc: self }
    }
}

/// Read-only handle to a [`GcWorld`].
///
/// Created via [`GcWorld::read_only`]. While alive, blocks all mutation through the
/// owning `GcWorld` (runtime check), and enables [`CRef::read_bypass`] for cheap,
/// scope-lifetime `&T` access that bypasses the dynamic borrow counter.
pub struct ReadWorld<'a> {
    gc: &'a GcWorld,
}

impl<'a> ReadWorld<'a> {
    #[inline]
    pub(crate) fn world_slot(&self) -> NonZeroU32 {
        self.gc.world.world_slot()
    }

    /// Returns a `CRef` to the `T` component of `entity`.
    pub fn get<T: Component>(&self, entity: Entity) -> Result<CRef<T>, ComponentError> {
        self.gc.get::<T>(entity)
    }

    /// Resolve entity location, returning `Err` if despawned.
    fn resolve(&self, entity: Entity) -> Result<(&Archetype, u32), NoSuchEntity> {
        let loc = self.gc.world.entities().get(entity)?;
        let archetype = &self.gc.world.archetypes_inner()[loc.archetype];
        if archetype.entity(loc.index).id == u32::MAX {
            return Err(NoSuchEntity);
        }
        Ok((archetype, loc.index))
    }

    /// Returns an [`EntityRef`] for the given entity.
    pub fn entity(&self, entity: Entity) -> Result<EntityRef<'_>, NoSuchEntity> {
        let (archetype, index) = self.resolve(entity)?;
        Ok(EntityRef {
            archetype,
            entity,
            index,
        })
    }

    /// Returns `true` if `entity` satisfies the query `Q`.
    pub fn satisfies<Q: Query>(&self, entity: Entity) -> Result<bool, NoSuchEntity> {
        let e = self.entity(entity)?;
        Ok(Q::Fetch::prepare(e.archetype()).is_some())
    }

    /// Whether `entity` exists.
    pub fn contains(&self, entity: Entity) -> bool {
        self.resolve(entity).is_ok()
    }

    /// Query a single entity.
    pub fn query_one<Q: Query>(&self, entity: Entity) -> Result<QueryItem<'_, Q>, QueryOneError> {
        let (archetype, index) = self.resolve(entity)?;
        let state = Q::Fetch::prepare(archetype).ok_or(QueryOneError::Unsatisfied)?;
        let fetch = Q::Fetch::execute(archetype, state);
        unsafe { Ok(fetch.get(index as usize)) }
    }

    /// Iterate over all entities matching `Q`. See [`GcWorld::query`].
    pub fn query<Q: Query>(&self) -> QueryBorrow<'_, Q> {
        QueryBorrow::new(
            &self.gc.world.entities().meta,
            self.gc.world.archetypes_inner().iter(),
        )
    }

    /// Returns the number of entities in the world.
    pub fn len(&self) -> u32 {
        self.gc.world.len()
    }

    /// Returns `true` if the world contains no entities.
    pub fn is_empty(&self) -> bool {
        self.gc.world.is_empty()
    }
}

impl<'a> Drop for ReadWorld<'a> {
    fn drop(&mut self) {
        unsafe { super::exit_read_only(self.gc.world.world_slot()) };
    }
}

impl<'a> Drop for GcWorldScope<'a> {
    fn drop(&mut self) {
        // The original slot lives in `gc_world.world` until we swap it back.
        // Disable here so that after the swap, the user's `World` is left in `Off`.
        unsafe { super::disable_gc_borrows(self.gc_world.world.world_slot()) };
        core::mem::swap(self.original_world_ref, &mut self.gc_world.world);
        // GcWorld::Drop will then run on the temp World's slot, which was never
        // enabled — harmless no-op.
    }
}

impl Drop for GcWorld {
    fn drop(&mut self) {
        unsafe { super::disable_gc_borrows(self.world.world_slot()) };
    }
}

#[derive(Copy, Clone)]
pub struct EntityRef<'a> {
    archetype: &'a Archetype,
    entity: Entity,
    index: u32,
}

impl<'a> EntityRef<'a> {
    #[inline]
    pub fn entity(&self) -> Entity {
        self.entity
    }

    /// Determine whether this entity has a `T` component without borrowing it
    ///
    /// Equivalent to [`satisfies::<&T>`](Self::satisfies)
    pub fn has<T: Component>(&self) -> bool {
        self.archetype.has::<T>()
    }

    /// Borrow the component of type `T`, if it exists
    pub fn get<T: Component>(&self) -> Result<CRef<T>, MissingComponent> {
        let gc_ptr = unsafe {
            self.archetype
                .get_dynamic(&TypeInfo::of::<T>(), self.index)
        };
        gc_ptr
            .map(|ptr| CRef {
                ptr,
                _marker: PhantomData,
            })
            .ok_or(MissingComponent::new::<T>())
    }

    pub(crate) fn archetype(&self) -> &Archetype {
        &self.archetype
    }
    pub(crate) fn index(&self) -> u32 {
        self.index
    }
}

#[cfg(test)]
mod tests {
    use crate::{World, GcWorld, QueryOneError};

    #[test]
    fn len_and_is_empty() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            assert!(gc.is_empty());
            assert_eq!(gc.len(), 0);
            gc.spawn((1i32,));
            gc.spawn((2i32,));
            assert_eq!(gc.len(), 2);
            assert!(!gc.is_empty());
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn entity_ref_get() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32, true));
            let entity_ref = gc.entity(e).unwrap();
            assert!(entity_ref.has::<i32>());
            assert!(!entity_ref.has::<f32>());
            let val = entity_ref.get::<i32>().unwrap();
            assert_eq!(*val.read(), 42);
            let val = entity_ref.get::<bool>().unwrap();
            assert_eq!(*val.read(), true);
            assert!(entity_ref.get::<f32>().is_err());
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn satisfies() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32, true));
            assert!(gc.satisfies::<(&i32,)>(e).unwrap());
            assert!(gc.satisfies::<(&i32, &bool)>(e).unwrap());
            assert!(!gc.satisfies::<(&f32,)>(e).unwrap());
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn query_one() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32, 3.14f32));
            let (i, f) = gc.query_one::<(&i32, &f32)>(e).unwrap();
            assert_eq!(*i.read(), 42);
            assert_eq!(*f.read(), 3.14f32);
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn query_one_unsatisfied() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32,));
            let result = gc.query_one::<(&f32,)>(e);
            assert!(matches!(result, Err(QueryOneError::Unsatisfied)));
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn query_one_no_such_entity() {
        let mut world = World::new();
        let stale = world.spawn((42i32,));
        world.despawn(stale).unwrap();
        {
            let gc = GcWorld::new_scope(&mut world);
            let result = gc.query_one::<(&i32,)>(stale);
            assert!(matches!(result, Err(QueryOneError::NoSuchEntity)));
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn contains_and_entity_detect_nonsync_despawn() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32,));
            assert!(gc.contains(e));
            assert!(gc.entity(e).is_ok());
            gc.despawn(e).unwrap();
            assert!(!gc.contains(e));
            assert!(gc.entity(e).is_err());
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn query_one_after_nonsync_despawn() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32,));
            assert!(gc.query_one::<(&i32,)>(e).is_ok());
            gc.despawn(e).unwrap();
            assert!(matches!(
                gc.query_one::<(&i32,)>(e),
                Err(QueryOneError::NoSuchEntity)
            ));
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn entity_ref_after_sync_despawn() {
        let mut world = World::new();
        let e = world.spawn((42i32,));
        world.despawn(e).unwrap();
        {
            let gc = GcWorld::new_scope(&mut world);
            assert!(gc.entity(e).is_err());
            assert!(!gc.contains(e));
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn read_world_read_bypass_and_read() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32, true));
            let c = gc.get::<i32>(e).unwrap();
            {
                let read = gc.read_only();
                // Cheap path: scope-lifetime &T, no borrow-counter traffic.
                let v: &i32 = c.read_bypass(&read);
                assert_eq!(*v, 42);
                // Dynamic path still works in ReadOnly mode and uses the borrow counter
                // exactly as in GcDynamic mode.
                assert_eq!(*c.read(), 42);
                // ReadWorld's own lookup API returns CRef<T>.
                let c2 = read.get::<i32>(e).unwrap();
                assert_eq!(*c2.read_bypass(&read), 42);
            }
            // Back to GcDynamic — writes work again.
            *c.write() = 100;
            assert_eq!(*c.read(), 100);
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn read_world_nested_scopes() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((42i32,));
            let c = gc.get::<i32>(e).unwrap();
            let outer = gc.read_only();
            {
                let inner = gc.read_only();
                assert_eq!(*c.read_bypass(&inner), 42);
                assert_eq!(*c.read_bypass(&outer), 42);
            }
            // Still in ReadOnly because outer is alive.
            assert_eq!(*c.read_bypass(&outer), 42);
            drop(outer);
            // Back to GcDynamic.
            *c.write() = 7;
            assert_eq!(*c.read(), 7);
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    fn read_world_query() {
        use alloc::vec;
        use alloc::vec::Vec;
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let a = gc.spawn((1i32, true));
            let b = gc.spawn((2i32, false));
            gc.spawn((3i32,)); // missing bool
            let read = gc.read_only();
            let mut found = Vec::new();
            for (e, (i, b_)) in read.query::<(&i32, &bool)>().iter() {
                found.push((e, *i.read_bypass(&read), *b_.read_bypass(&read)));
            }
            found.sort_by_key(|t| t.1);
            assert_eq!(found, vec![(a, 1, true), (b, 2, false)]);
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    #[should_panic(expected = "GcWorld mutation attempted while a ReadWorld scope is active")]
    fn read_world_blocks_spawn() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let _read = gc.read_only();
            gc.spawn((1i32,));
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    #[should_panic(expected = "GcWorld mutation attempted while a ReadWorld scope is active")]
    fn read_world_blocks_despawn() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((1i32,));
            let _read = gc.read_only();
            gc.despawn(e).unwrap();
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    #[should_panic(expected = "CRef::write during ReadWorld scope")]
    fn read_world_blocks_cref_write() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((1i32,));
            let c = gc.get::<i32>(e).unwrap();
            let _read = gc.read_only();
            let _w = c.write();
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    #[should_panic(expected = "CRef::read_bypass while a mutable borrow is held")]
    fn read_bypass_rejects_active_refmut() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((1i32,));
            let c = gc.get::<i32>(e).unwrap();
            let _w = c.write(); // RefMut held across scope entry
            let read = gc.read_only();
            let _v: &i32 = c.read_bypass(&read);
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    #[should_panic(expected = "CRef::write during ReadWorld scope")]
    fn leaked_read_world_does_not_poison_next_scope() {
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let read = gc.read_only();
            // Skip ReadWorld's Drop — depth would naively stay at 1 forever.
            core::mem::forget(read);
        }
        // New GcWorld lifecycle on the same slot. enable_gc_borrows must reset depth
        // so the next read_only() correctly transitions GcDynamic -> ReadOnly. If it
        // doesn't, c.write() below would succeed and we'd silently have UB.
        let gc = GcWorld::new_scope(&mut world);
        let e = gc.spawn((1i32,));
        let c = gc.get::<i32>(e).unwrap();
        let _read = gc.read_only();
        let _w = c.write();
    }

    #[test]
    fn leaked_read_world_does_not_block_next_scope_mutation() {
        // Symmetric positive check: after a forgotten ReadWorld, the next scope's
        // GcDynamic operations (spawn / despawn) work normally.
        let mut world = World::new();
        {
            let gc = GcWorld::new_scope(&mut world);
            let read = gc.read_only();
            core::mem::forget(read);
        }
        {
            let gc = GcWorld::new_scope(&mut world);
            let e = gc.spawn((1i32,));
            gc.despawn(e).unwrap();
        }
        crate::world::tests::cleanup(world);
    }

    #[test]
    #[should_panic(expected = "CRef belongs to a different World")]
    fn read_bypass_rejects_foreign_world_scope() {
        let mut world_a = World::new();
        let mut world_b = World::new();
        {
            let gc_a = GcWorld::new_scope(&mut world_a);
            let gc_b = GcWorld::new_scope(&mut world_b);
            let e_a = gc_a.spawn((1i32,));
            let c_a = gc_a.get::<i32>(e_a).unwrap();
            let read_b = gc_b.read_only();
            let _v: &i32 = c_a.read_bypass(&read_b);
        }
        crate::world::tests::cleanup(world_a);
        crate::world::tests::cleanup(world_b);
    }
}
