use core::cell::RefCell;
use core::slice::Iter as SliceIter;
use core::{marker::PhantomData, ptr::NonNull};

use alloc::rc::Rc;

use crate::archetype::Data;
use crate::{entities::EntityMeta, Archetype, Component, Entity};
use crate::{CRef, ComponentError, MissingComponent, TypeInfo};

/// Errors that arise when fetching
#[derive(Debug, Clone, Eq, PartialEq)]
#[doc(hidden)]
pub enum FetchError {
    /// The entity was already despawned
    NoSuchEntity,
    /// The entity did not have a requested component
    MissingComponent(MissingComponent),
    /// The entity no longer matches the query, happens with Without
    InvalidMatch,
}

impl From<ComponentError> for FetchError {
    fn from(e: ComponentError) -> Self {
        match e {
            ComponentError::NoSuchEntity => Self::NoSuchEntity,
            ComponentError::MissingComponent(c) => Self::MissingComponent(c),
        }
    }
}

/// A collection of component types to fetch from a [`World`](crate::World)
///
/// The interface of this trait is a private implementation detail.
pub trait Query {
    #[doc(hidden)]
    type Fetch: for<'a> Fetch<'a>;
}

/// Type of values yielded by a query
///
/// Once rust offers generic associated types, this will be moved into [`Query`].
pub type QueryItem<'a, Q> = <<Q as Query>::Fetch as Fetch<'a>>::Item;

/// Streaming iterators over contiguous homogeneous ranges of components
#[allow(clippy::missing_safety_doc)]
pub unsafe trait Fetch<'a>: Sized {
    /// Type of value to be fetched
    type Item;

    /// The type of the data which can be cached to speed up retrieving
    /// the relevant type states from a matching [`Archetype`]
    type State: Copy;

    /// A value on which `get` may never be called
    fn dangling() -> Self;

    /// Look up state for `archetype` if it should be traversed
    fn prepare(archetype: &Archetype) -> Option<Self::State>;
    /// Construct a `Fetch` for `archetype` based on the associated state
    fn execute(archetype: &'a Archetype, state: Self::State) -> Self;

    /// Access the `n`th item in this archetype without bounds checking
    ///
    /// # Safety
    /// - Must only be called after `borrow`
    /// - `release` must not be called while `'a` is still live
    /// - Bounds-checking must be performed externally
    /// - Any resulting borrows must be legal (e.g. no &mut to something another iterator might access)
    unsafe fn get(&self, n: usize) -> Self::Item;
}

impl<'a, T: Component> Query for &'a T {
    type Fetch = FetchGet<T>;
}

impl<'a, T: Component> Query for &'a mut T {
    type Fetch = FetchGet<T>;
}

#[doc(hidden)]
pub struct FetchGet<T> {
    data: NonNull<Data>,
    _marker: PhantomData<T>,
}

unsafe impl<'a, T: Component> Fetch<'a> for FetchGet<T> {
    type Item = CRef<T>;

    type State = usize;

    fn dangling() -> Self {
        Self {
            data: NonNull::dangling(),
            _marker: PhantomData::default(),
        }
    }

    fn prepare(archetype: &Archetype) -> Option<Self::State> {
        archetype.get_state::<T>()
    }
    fn execute(archetype: &'a Archetype, state: Self::State) -> Self {
        unsafe {
            Self {
                data: NonNull::new_unchecked(
                    archetype.get_data_storage(state) as *const Data as *mut Data
                ),
                _marker: PhantomData::default(),
            }
        }
    }

    unsafe fn get(&self, n: usize) -> Self::Item {
        CRef {
            ptr: self.data.as_ref().get_gc_ptr(n as u32),
            _marker: PhantomData::default(),
        }
    }
}

impl<T: Query> Query for Option<T> {
    type Fetch = TryFetch<T::Fetch>;
}

#[doc(hidden)]
pub struct TryFetch<T>(Option<T>);

unsafe impl<'a, T: Fetch<'a>> Fetch<'a> for TryFetch<T> {
    type Item = Option<T::Item>;

    type State = Option<T::State>;

    fn dangling() -> Self {
        Self(None)
    }

    fn prepare(archetype: &Archetype) -> Option<Self::State> {
        Some(T::prepare(archetype))
    }
    fn execute(archetype: &'a Archetype, state: Self::State) -> Self {
        Self(state.map(|state| T::execute(archetype, state)))
    }

    unsafe fn get(&self, n: usize) -> Option<T::Item> {
        Some(self.0.as_ref()?.get(n))
    }
}

/// Holds an `L`, or an `R`, or both
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Or<L, R> {
    /// Just an `L`
    Left(L),
    /// Just an `R`
    Right(R),
    /// Both an `L` and an `R`
    Both(L, R),
}

impl<L, R> Or<L, R> {
    /// Construct an `Or<L, R>` if at least one argument is `Some`
    pub fn new(l: Option<L>, r: Option<R>) -> Option<Self> {
        match (l, r) {
            (None, None) => None,
            (Some(l), None) => Some(Or::Left(l)),
            (None, Some(r)) => Some(Or::Right(r)),
            (Some(l), Some(r)) => Some(Or::Both(l, r)),
        }
    }

    /// Destructure into two `Option`s, where either or both are `Some`
    pub fn split(self) -> (Option<L>, Option<R>) {
        match self {
            Or::Left(l) => (Some(l), None),
            Or::Right(r) => (None, Some(r)),
            Or::Both(l, r) => (Some(l), Some(r)),
        }
    }

    /// Extract `L` regardless of whether `R` is present
    pub fn left(self) -> Option<L> {
        match self {
            Or::Left(l) => Some(l),
            Or::Both(l, _) => Some(l),
            _ => None,
        }
    }

    /// Extract `R` regardless of whether `L` is present
    pub fn right(self) -> Option<R> {
        match self {
            Or::Right(r) => Some(r),
            Or::Both(_, r) => Some(r),
            _ => None,
        }
    }

    /// Transform `L` with `f` and `R` with `g`
    pub fn map<L1, R1, F, G>(self, f: F, g: G) -> Or<L1, R1>
    where
        F: FnOnce(L) -> L1,
        G: FnOnce(R) -> R1,
    {
        match self {
            Or::Left(l) => Or::Left(f(l)),
            Or::Right(r) => Or::Right(g(r)),
            Or::Both(l, r) => Or::Both(f(l), g(r)),
        }
    }

    /// Convert from `&Or<L, R>` to `Or<&L, &R>`
    pub fn as_ref(&self) -> Or<&L, &R> {
        match *self {
            Or::Left(ref l) => Or::Left(l),
            Or::Right(ref r) => Or::Right(r),
            Or::Both(ref l, ref r) => Or::Both(l, r),
        }
    }
}

impl<L, R> Or<&'_ L, &'_ R>
where
    L: Clone,
    R: Clone,
{
    /// Maps an `Or<&L, &R>` to an `Or<L, R>` by cloning its contents
    pub fn cloned(self) -> Or<L, R> {
        self.map(Clone::clone, Clone::clone)
    }
}

impl<L: Query, R: Query> Query for Or<L, R> {
    type Fetch = FetchOr<L::Fetch, R::Fetch>;
}

#[doc(hidden)]
pub struct FetchOr<L, R>(Or<L, R>);

unsafe impl<'a, L: Fetch<'a>, R: Fetch<'a>> Fetch<'a> for FetchOr<L, R> {
    type Item = Or<L::Item, R::Item>;

    type State = Or<L::State, R::State>;

    fn dangling() -> Self {
        Self(Or::Left(L::dangling()))
    }

    fn prepare(archetype: &Archetype) -> Option<Self::State> {
        Or::new(L::prepare(archetype), R::prepare(archetype))
    }

    fn execute(archetype: &'a Archetype, state: Self::State) -> Self {
        Self(state.map(|l| L::execute(archetype, l), |r| R::execute(archetype, r)))
    }

    unsafe fn get(&self, n: usize) -> Self::Item {
        self.0.as_ref().map(|l| l.get(n), |r| r.get(n))
    }
}

/// Query transformer skipping entities that have a `T` component
///
/// See also `QueryBorrow::without`.
///
/// # Example
/// ```
/// # use hecs::ergo::*;
/// let mut world = World::new();
/// let a = world.spawn((123, true, "abc"));
/// let b = world.spawn((456, false));
/// let c = world.spawn((42, "def"));
/// let ergo = GCWorld::new(&mut world);
/// let entities = ergo.query::<Without<&i32, &bool>>()
///     .iter()
///     .map(|(e, i)| (e, *i.read()))
///     .collect::<Vec<_>>();
/// assert_eq!(entities, &[(c, 42)]);
/// ```
pub struct Without<Q, R>(PhantomData<(Q, fn(R))>);

impl<Q: Query, R: Query> Query for Without<Q, R> {
    type Fetch = FetchWithout<Q::Fetch, R::Fetch>;
}

#[doc(hidden)]
pub struct FetchWithout<F, G>(F, PhantomData<fn(G)>);

unsafe impl<'a, F: Fetch<'a>, G: Fetch<'a>> Fetch<'a> for FetchWithout<F, G> {
    type Item = F::Item;

    type State = F::State;

    fn dangling() -> Self {
        Self(F::dangling(), PhantomData)
    }

    fn prepare(archetype: &Archetype) -> Option<Self::State> {
        if G::prepare(archetype).is_some() {
            return None;
        }
        F::prepare(archetype)
    }
    fn execute(archetype: &'a Archetype, state: Self::State) -> Self {
        Self(F::execute(archetype, state), PhantomData)
    }

    unsafe fn get(&self, n: usize) -> F::Item {
        self.0.get(n)
    }
}

/// Query transformer skipping entities that do not have a `T` component
///
/// See also `QueryBorrow::with`.
///
/// # Example
/// ```
/// # use hecs::ergo::*;
/// let mut world = World::new();
/// let a = world.spawn((123, true, "abc"));
/// let b = world.spawn((456, false));
/// let c = world.spawn((42, "def"));
/// let ergo = GCWorld::new(&mut world);
/// let entities = ergo.query::<With<&i32, &bool>>()
///     .iter()
///     .map(|(e, i)| (e, *i.read()))
///     .collect::<Vec<_>>();
/// assert_eq!(entities.len(), 2);
/// assert!(entities.contains(&(a, 123)));
/// assert!(entities.contains(&(b, 456)));
/// ```
pub struct With<Q, R>(PhantomData<(Q, fn(R))>);

impl<Q: Query, R: Query> Query for With<Q, R> {
    type Fetch = FetchWith<Q::Fetch, R::Fetch>;
}

#[doc(hidden)]
pub struct FetchWith<F, G>(F, PhantomData<fn(G)>);

unsafe impl<'a, F: Fetch<'a>, G: Fetch<'a>> Fetch<'a> for FetchWith<F, G> {
    type Item = F::Item;

    type State = F::State;

    fn dangling() -> Self {
        Self(F::dangling(), PhantomData)
    }

    fn prepare(archetype: &Archetype) -> Option<Self::State> {
        G::prepare(archetype)?;
        F::prepare(archetype)
    }
    fn execute(archetype: &'a Archetype, state: Self::State) -> Self {
        Self(F::execute(archetype, state), PhantomData)
    }

    unsafe fn get(&self, n: usize) -> F::Item {
        self.0.get(n)
    }
}

/// A query that yields `true` iff an entity would satisfy the query `Q`
///
/// Does not borrow any components, making it faster and more concurrency-friendly than `Option<Q>`.
///
/// # Example
/// ```
/// # use hecs::ergo::*;
/// let mut world = World::new();
/// let a = world.spawn((123, true, "abc"));
/// let b = world.spawn((456, false));
/// let c = world.spawn((42, "def"));
/// let ergo = GCWorld::new(&mut world);
/// let entities = ergo.query::<Satisfies<&bool>>()
///     .iter()
///     .map(|(e, x)| (e, x))
///     .collect::<Vec<_>>();
/// assert_eq!(entities.len(), 3);
/// assert!(entities.contains(&(a, true)));
/// assert!(entities.contains(&(b, true)));
/// assert!(entities.contains(&(c, false)));
/// ```
pub struct Satisfies<Q>(PhantomData<Q>);

impl<Q: Query> Query for Satisfies<Q> {
    type Fetch = FetchSatisfies<Q::Fetch>;
}

#[doc(hidden)]
pub struct FetchSatisfies<F>(bool, PhantomData<F>);

unsafe impl<'a, F: Fetch<'a>> Fetch<'a> for FetchSatisfies<F> {
    type Item = bool;

    type State = bool;

    fn dangling() -> Self {
        Self(false, PhantomData)
    }

    fn prepare(archetype: &Archetype) -> Option<Self::State> {
        Some(F::prepare(archetype).is_some())
    }
    fn execute(_archetype: &'a Archetype, state: Self::State) -> Self {
        Self(state, PhantomData)
    }

    unsafe fn get(&self, _: usize) -> bool {
        self.0
    }
}

/// A borrow of a [`World`](crate::World) sufficient to execute the query `Q`
///
/// Note that borrows are not released until this object is dropped.
pub struct QueryBorrow<'w, Q: Query> {
    meta: &'w [EntityMeta],
    archetypes: &'w [Archetype],
    _marker: PhantomData<Q>,
}

impl<'w, Q: Query> QueryBorrow<'w, Q> {
    pub(crate) fn new(meta: &'w [EntityMeta], archetypes: &'w [Archetype]) -> Self {
        Self {
            meta,
            archetypes,
            _marker: PhantomData,
        }
    }

    /// Execute the query
    // The lifetime narrowing here is required for soundness.
    pub fn iter(&mut self) -> QueryIter<'_, Q> {
        unsafe { QueryIter::new(self.meta, self.archetypes.iter()) }
    }

    /// Transform the query into one that requires a certain component without borrowing it
    ///
    /// This can be useful when the component needs to be borrowed elsewhere and it isn't necessary
    /// for the iterator to expose its data directly.
    ///
    /// Equivalent to using a query type wrapped in `With`.
    ///
    /// # Example
    /// ```
    /// # use hecs::ergo::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, true, "abc"));
    /// let b = world.spawn((456, false));
    /// let c = world.spawn((42, "def"));
    /// let ergo = GCWorld::new(&mut world);
    /// let entities = ergo.query::<&i32>()
    ///     .with::<&bool>()
    ///     .iter()
    ///     .map(|(e, i)| (e, *i.read())) // Copy out of the world
    ///     .collect::<Vec<_>>();
    /// assert!(entities.contains(&(a, 123)));
    /// assert!(entities.contains(&(b, 456)));
    /// ```
    pub fn with<R: Query>(self) -> QueryBorrow<'w, With<Q, R>> {
        self.transform()
    }

    /// Transform the query into one that skips entities having a certain component
    ///
    /// Equivalent to using a query type wrapped in `Without`.
    ///
    /// # Example
    /// ```
    /// # use hecs::ergo::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, true, "abc"));
    /// let b = world.spawn((456, false));
    /// let c = world.spawn((42, "def"));
    /// let ergo = GCWorld::new(&mut world);
    /// let entities = ergo.query::<&i32>()
    ///     .without::<&bool>()
    ///     .iter()
    ///     .map(|(e, i)| (e, *i.read())) // Copy out of the world
    ///     .collect::<Vec<_>>();
    /// assert_eq!(entities, &[(c, 42)]);
    /// ```
    pub fn without<R: Query>(self) -> QueryBorrow<'w, Without<Q, R>> {
        self.transform()
    }

    // TODO implement
    /// Determine whether this entity would satisfy the query `Q`
    // pub fn satisfies<R: Query>(&self) -> bool {
    //     R::Fetch::prepare(self.archetype).is_some()
    // }

    /// Helper to change the type of the query
    fn transform<R: Query>(self) -> QueryBorrow<'w, R> {
        QueryBorrow {
            meta: self.meta,
            archetypes: self.archetypes,
            _marker: PhantomData,
        }
    }
}

impl<'q, 'w: 'q, Q: Query> IntoIterator for &'q mut QueryBorrow<'w, Q> {
    type Item = (Entity, QueryItem<'q, Q>);
    type IntoIter = QueryIter<'q, Q>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over the set of entities with the components in `Q`
pub struct QueryIter<'q, Q: Query> {
    meta: &'q [EntityMeta],
    archetypes: SliceIter<'q, Archetype>,
    iter: ChunkIter<Q>,
}

impl<'q, Q: Query> QueryIter<'q, Q> {
    /// # Safety
    ///
    /// `'q` must be sufficient to guarantee that `Q` cannot violate borrow safety, either with
    /// dynamic borrow checks or by representing exclusive access to the `World`.
    unsafe fn new(meta: &'q [EntityMeta], archetypes: SliceIter<'q, Archetype>) -> Self {
        Self {
            meta,
            archetypes,
            iter: ChunkIter::empty(),
        }
    }
}

unsafe impl<'q, Q: Query> Send for QueryIter<'q, Q> where <Q::Fetch as Fetch<'q>>::Item: Send {}
unsafe impl<'q, Q: Query> Sync for QueryIter<'q, Q> where <Q::Fetch as Fetch<'q>>::Item: Send {}

impl<'q, Q: Query> Iterator for QueryIter<'q, Q> {
    type Item = (Entity, QueryItem<'q, Q>);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match unsafe { self.iter.next() } {
                None => {
                    let archetype = self.archetypes.next()?;
                    let state = Q::Fetch::prepare(archetype);
                    let fetch = state.map(|state| Q::Fetch::execute(archetype, state));
                    self.iter = fetch.map_or(ChunkIter::empty(), |fetch| ChunkIter {
                        entities: archetype.entities(),
                        fetch,
                        position: 0,
                        len: archetype.len_sync() as usize,
                    });
                    continue;
                }
                Some((id, components)) => {
                    if id == u32::MAX {
                        continue;
                    }
                    return Some((
                        Entity {
                            id,
                            generation: unsafe { self.meta.get_unchecked(id as usize).generation },
                        },
                        components,
                    ));
                }
            }
        }
    }
}

struct ChunkIter<Q: Query> {
    entities: NonNull<u32>,
    fetch: Q::Fetch,
    position: usize,
    len: usize,
}

impl<Q: Query> ChunkIter<Q> {
    fn empty() -> Self {
        Self {
            entities: NonNull::dangling(),
            fetch: Q::Fetch::dangling(),
            position: 0,
            len: 0,
        }
    }

    #[inline]
    unsafe fn next<'a>(&mut self) -> Option<(u32, <Q::Fetch as Fetch<'a>>::Item)> {
        while self.position < self.len {
            let entity = self.entities.as_ptr().add(self.position);
            let pos = self.position;
            self.position += 1;
            if *entity == u32::MAX {
                continue;
            }
            let item = self.fetch.get(pos);
            return Some((*entity, item));
        }
        None
    }
}

macro_rules! tuple_impl {
    ($($name: ident),*) => {
        unsafe impl<'a, $($name: Fetch<'a>),*> Fetch<'a> for ($($name,)*) {
            type Item = ($($name::Item,)*);

            type State = ($($name::State,)*);

            #[allow(clippy::unused_unit)]
            fn dangling() -> Self {
                ($($name::dangling(),)*)
            }

            #[allow(unused_variables)]
            fn prepare(archetype: &Archetype) -> Option<Self::State> {
                Some(($($name::prepare(archetype)?,)*))
            }
            #[allow(unused_variables, non_snake_case, clippy::unused_unit)]
            fn execute(archetype: &'a Archetype, state: Self::State) -> Self {
                let ($($name,)*) = state;
                ($(<$name as Fetch<'a>>::execute(archetype, $name),)*)
            }

            #[allow(unused_variables, clippy::unused_unit)]
            unsafe fn get(&self,  n: usize) -> Self::Item {
                #[allow(non_snake_case)]
                let ($($name,)*) = self;
                ($($name.get(n),)*)
            }
        }

        impl<$($name: Query),*> Query for ($($name,)*) {
            type Fetch = ($($name::Fetch,)*);
        }
    };
}

smaller_tuples_too!(tuple_impl, O, N, M, L, K, J, I, H, G, F, E, D, C, B, A);
#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use crate::{GCWorld, World};

    #[test]
    fn ergo_query_iter() {
        let mut world = World::new();
        let e1 = world.spawn((5i32, 1.5f32));
        let e2 = world.spawn((6i32, 2.5f32));
        assert!(world.len() == 2);
        let ergo_scope = GCWorld::new(&mut world);
        let entities = ergo_scope
            .query::<(&i32, &f32)>()
            .iter()
            .map(|(e, (i, b))| (e, i, b)) // Copy out of the world
            .collect::<Vec<_>>();
        assert!(entities.len() == 2);

        assert_eq!(entities[0].0, e1);
        assert_eq!(*entities[0].1.read(), 5i32);
        assert_eq!(*entities[0].2.read(), 1.5f32);

        assert_eq!(entities[1].0, e2);
        assert_eq!(*entities[1].1.read(), 6i32);
        assert_eq!(*entities[1].2.read(), 2.5f32);
    }

    // #[test]
    // fn ergo_query_iter_remove() {
    //     let mut world = World::new();
    //     let e1 = world.spawn((5i32, 1.5f32));
    //     let e2 = world.spawn((6i32, 2.5f32));
    //     assert!(world.len() == 2);
    //     let ergo_scope = GCWorld::new(&mut world);
    //     let mut query = ergo_scope.query::<(&i32, &f32)>();
    //     let mut entities = query.iter();

    //     ergo_scope.despawn(e1).expect("failed to despawn entity");

    //     let (entity, (c2, d2)) = entities.next().expect("expected entity");
    //     assert_eq!(entity, e2);
    //     assert_eq!(*c2.read(), 6i32);
    //     assert_eq!(*d2.read(), 2.5f32);

    //     assert!(entities.next().is_none());
    // }

    // #[test]
    // fn ergo_query_iter_insert() {
    //     let mut world = World::new();
    //     let e1 = world.spawn((5i32, 1.5f32));
    //     let e2 = world.spawn((6i32,));
    //     assert!(world.len() == 2);
    //     let ergo_scope = GCWorld::new(&mut world);
    //     let mut query = ergo_scope.query::<(&i32, &f32)>();
    //     let mut entities = query.iter();

    //     let (entity, (c1, d1)) = entities.next().expect("expected entity 1");
    //     assert_eq!(entity, e1);
    //     assert_eq!(*c1.read(), 5i32);
    //     assert_eq!(*d1.read(), 1.5f32);

    //     ergo_scope
    //         .insert(e2, (2.5f32,))
    //         .expect("failed to insert component");

    //     let (entity, (c2, d2)) = entities.next().expect("expected entity 2");
    //     assert_eq!(entity, e2);
    //     assert_eq!(*c2.read(), 6i32);
    //     assert_eq!(*d2.read(), 2.5f32);

    //     ergo_scope
    //         .insert(e2, (4.5f32,))
    //         .expect("failed to insert component");

    //     assert!(entities.next().is_none());
    // }

    // #[test]
    // fn ergo_query_iter_insert_remove() {
    //     let mut world = World::new();
    //     let e1 = world.spawn((5i32, 1.5f32));
    //     let e2 = world.spawn((6i32,));
    //     assert!(world.len() == 2);
    //     let ergo_scope = GCWorld::new(&mut world);
    //     let mut query = ergo_scope.query::<(&i32, &f32)>();
    //     let mut entities = query.iter();

    //     let (entity, _) = entities.next().expect("expected entity 1");
    //     assert_eq!(entity, e1);

    //     ergo_scope
    //         .insert(e2, (2.5f32,))
    //         .expect("failed to insert component");

    //     ergo_scope
    //         .remove::<(f32,)>(e2)
    //         .expect("failed to remove component");

    //     assert!(entities.next().is_none());
    // }

    // #[test]
    // fn ergo_query_iter_remove_insert() {
    //     let mut world = World::new();
    //     let e1 = world.spawn((5i32, 1.5f32));
    //     let e2 = world.spawn((6i32, 1.8f32));
    //     assert!(world.len() == 2);
    //     let ergo_scope = GCWorld::new(&mut world);
    //     let mut query = ergo_scope.query::<(&i32, &f32)>();
    //     let mut entities = query.iter();

    //     let (entity, _) = entities.next().expect("expected entity 1");
    //     assert_eq!(entity, e1);

    //     let (entity, _) = entities.next().expect("expected entity 2");
    //     assert_eq!(entity, e2);

    //     ergo_scope
    //         .remove::<(f32,)>(e2)
    //         .expect("failed to remove component");

    //     ergo_scope
    //         .insert(e2, (2.5f32,))
    //         .expect("failed to insert component");

    //     assert!(entities.next().is_none());
    // }

    // #[test]
    // fn ergo_query_iter_despawn() {
    //     let mut world = World::new();
    //     let e1 = world.spawn((5i32, 1.5f32));
    //     let e2 = world.spawn((6i32, 1.8f32));
    //     assert!(world.len() == 2);
    //     let ergo_scope = GCWorld::new(&mut world);
    //     let mut query = ergo_scope.query::<(&i32, &f32)>();
    //     let mut entities = query.iter();

    //     let (entity, _) = entities.next().expect("expected entity 1");
    //     assert_eq!(entity, e1);

    //     ergo_scope.despawn(e2).expect("failed to despawn");

    //     assert!(entities.next().is_none());
    // }
}
