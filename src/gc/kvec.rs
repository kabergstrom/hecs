use core::{
    alloc::Layout,
    cell::RefCell,
    cmp,
    marker::PhantomData,
    mem::{self, size_of},
    ops::{self, Index, IndexMut, Range},
    ptr::{self, null, null_mut, NonNull},
    slice::{self, SliceIndex},
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};
use std::sync::Mutex;

use alloc::{alloc::dealloc, vec::Vec};

use super::cells::{PtrCell, UsizeCell};

pub trait SizedTypeProperties: Sized {
    #[doc(hidden)]
    const IS_ZST: bool = size_of::<Self>() == 0;
}

struct AllocHeader {
    cap: usize,
    reserved: UsizeCell,
    written: UsizeCell,
}

#[doc(hidden)]
impl<T> SizedTypeProperties for T {}
// SAFETY: `KVec` owns its `T`s yet is `Send + Sync` for any `T: Clone`, with no `T: Send` /
// `T: Sync` bound. A bound is not added because one of its four uses, the chunk table
// `Data::storage: KVec<*mut u8>`, holds raw pointers, which are neither; the other uses
// (`EntityCell`, `EntityMeta`, `u32`) are plain data. It is sound for those uses because
// (1) the chunk pointers are owned by the archetype, whose components are `Send + Sync`
// (`Component`), and (2) the safe `&self` API is `Deref` and `len_sync`, which read with
// acquire loads; every unsynchronized `&self` mutation is an `unsafe` `*_nonsync` method with
// an NS contract, which the engine meets by touching a `World` only on its owning thread (see
// the `Send` impl of `gc::GCPtr`). `KVec` is public but nothing outside hecs uses it; a new
// use with a non-thread-safe `T` must not rely on these impls.
// (The synchronized `*_sync` writers that once existed were broken and unused, and are gone.)
unsafe impl<T: Clone> Send for KVec<T> {}
unsafe impl<T: Clone> Sync for KVec<T> {}
pub struct KVec<T: Clone> {
    ptr: PtrCell<u8>,
    data_start: usize,
    old_allocs: Mutex<Vec<*mut u8>>,
    _marker: PhantomData<T>,
}

impl<T: Clone> Default for KVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Drop for KVec<T> {
    fn drop(&mut self) {
        self.clean_old_allocs();
        let current_alloc = self.ptr.read();
        if !current_alloc.is_null() {
            let header = unsafe { &mut *current_alloc.cast::<AllocHeader>() };
            let len = header.written.read();
            let data_ptr = unsafe { current_alloc.add(self.data_start) };
            let (layout, _) = Self::get_layout(header.cap);
            unsafe {
                core::ptr::drop_in_place(core::slice::from_raw_parts_mut(data_ptr, len));
                alloc::alloc::dealloc(current_alloc, layout)
            };
        }
    }
}

impl<T: Clone> KVec<T> {
    pub(crate) const MIN_NON_ZERO_CAP: usize = if mem::size_of::<T>() == 1 {
        8
    } else if mem::size_of::<T>() <= 1024 {
        4
    } else {
        1
    };
    pub fn new() -> Self {
        Self {
            ptr: PtrCell::new(null_mut()),
            data_start: Self::get_layout(2).1,
            old_allocs: Mutex::new(Vec::new()),
            _marker: PhantomData::default(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let ptr = Self::allocate(capacity);
        Self {
            ptr: PtrCell::new(ptr),
            data_start: Self::get_layout(2).1,
            old_allocs: Mutex::new(Vec::new()),
            _marker: PhantomData::default(),
        }
    }

    #[inline(always)]
    /// The data and header pointers of the current allocation (raw, with write permission).
    ///
    /// # Safety
    /// NS: no concurrent growth.
    unsafe fn current_memory_nonsync(&self) -> Option<(NonNull<T>, NonNull<AllocHeader>)> {
        if T::IS_ZST {
            None
        } else {
            let ptr = self.ptr.read_nonsync();
            if ptr.is_null() {
                return None;
            }
            let data_ptr = unsafe { ptr.add(self.data_start) };
            unsafe {
                Some((
                    NonNull::new_unchecked(data_ptr.cast::<T>()),
                    NonNull::new_unchecked(ptr.cast::<AllocHeader>()),
                ))
            }
        }
    }

    #[inline(always)]
    fn current_memory_sync(&self) -> Option<(NonNull<T>, NonNull<AllocHeader>)> {
        if T::IS_ZST {
            None
        } else {
            let ptr = self.ptr.load_atomic(Ordering::Relaxed);
            if ptr.is_null() {
                return None;
            }
            let data_ptr = unsafe { ptr.add(self.data_start) };
            unsafe {
                Some((
                    NonNull::new_unchecked(data_ptr.cast::<T>()),
                    NonNull::new_unchecked(ptr.cast::<AllocHeader>()),
                ))
            }
        }
    }

    /// Claim `additional` slots of `current`, or `None` if they don't fit.
    ///
    /// # Safety
    /// NS; `current` is this vector's live allocation header.
    #[inline(always)]
    unsafe fn reserve_slots_nonsync(
        current: Option<NonNull<AllocHeader>>,
        additional: usize,
    ) -> Option<Range<usize>> {
        if T::IS_ZST {
            return None;
        }
        if additional == 0 {
            return None;
        }
        if let Some(current) = current {
            let current = unsafe { current.as_ref() };
            let prev_len = current.reserved.read_nonsync();
            let capacity = current.cap;
            if additional > capacity.wrapping_sub(prev_len) {
                return None;
            }
            let new_len = prev_len.wrapping_add(additional);
            current.reserved.write_nonsync(new_len);
            Some(prev_len..new_len)
        } else {
            None
        }
    }

    fn grow_amortized(&mut self, cap: usize, len: usize, additional: usize) -> Option<*mut u8> {
        // This is ensured by the calling contexts.
        debug_assert!(additional > 0);

        if T::IS_ZST {
            // Since we return a capacity of `usize::MAX` when `elem_size` is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return None;
        }

        // Nothing we can really do about these checks, sadly.
        let required_cap = len.checked_add(additional)?;

        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap = cmp::max(cap * 2, required_cap);
        let cap = cmp::max(Self::MIN_NON_ZERO_CAP, cap);

        let ptr = Self::allocate(cap);
        if ptr.is_null() {
            return None;
        }
        let old_ptr = self.ptr.read();
        if !old_ptr.is_null() {
            let old_header = unsafe { &mut *old_ptr.cast::<AllocHeader>() }; // SAFETY: we have &mut self
            debug_assert_eq!(old_header.written.read(), old_header.reserved.read());
            unsafe {
                let written_len = old_header.written.read();
                // copy data from old to new allocation, and update length
                let src_data_ptr = old_ptr.add(self.data_start).cast::<T>();
                let dst_data_ptr = ptr.add(self.data_start).cast::<T>();
                for i in 0..written_len {
                    core::ptr::write(dst_data_ptr.add(i), (&*src_data_ptr.add(i)).clone());
                }
                let new_header = &mut *ptr.cast::<AllocHeader>();
                new_header.reserved.set(written_len);
                new_header.written.set(written_len);
            }
            self.old_allocs.lock().expect("lock poisoned").push(old_ptr);
        }
        self.ptr.set(ptr);
        Some(ptr)
    }

    /// Move to a larger allocation (cloning the elements). The old allocation is leaked, not
    /// freed, so outstanding `&T`/`&[T]` stay valid (but stale).
    ///
    /// # Safety
    /// NS; every reserved slot is written (`reserved == written`).
    unsafe fn grow_amortized_nonsync(
        &self,
        cap: usize,
        len: usize,
        additional: usize,
    ) -> Option<*mut u8> {
        // This is ensured by the calling contexts.
        debug_assert!(additional > 0);

        if T::IS_ZST {
            // Since we return a capacity of `usize::MAX` when `elem_size` is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return None;
        }

        // Nothing we can really do about these checks, sadly.
        let required_cap = len.checked_add(additional)?;

        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap = cmp::max(cap * 2, required_cap);
        let cap = cmp::max(Self::MIN_NON_ZERO_CAP, cap);

        let ptr = Self::allocate(cap);
        if ptr.is_null() {
            return None;
        }
        let old_ptr = self.ptr.read_nonsync();
        if !old_ptr.is_null() {
            let old_header = unsafe { &*old_ptr.cast::<AllocHeader>() };
            debug_assert!(old_header.written.read_nonsync() == old_header.reserved.read_nonsync());
            unsafe {
                let written_len = old_header.written.read_nonsync();
                // copy data from old to new allocation, and update length
                let src_data_ptr = old_ptr.add(self.data_start).cast::<T>();
                let dst_data_ptr = ptr.add(self.data_start).cast::<T>();
                for i in 0..written_len {
                    core::ptr::write(dst_data_ptr.add(i), (&*src_data_ptr.add(i)).clone());
                }
                let new_header = &*ptr.cast::<AllocHeader>();
                new_header.reserved.write_nonsync(written_len);
                new_header.written.write_nonsync(written_len);
            }
        }
        self.ptr.write_nonsync(ptr);
        Some(ptr)
    }

    fn get_layout(capacity: usize) -> (Layout, usize) {
        let layout = match Layout::array::<T>(capacity) {
            Ok(layout) => layout,
            Err(_) => panic!("capacity overflow"),
        };
        match Layout::new::<AllocHeader>().extend(layout) {
            Ok(v) => v,
            Err(_) => panic!("capacity_overflow"),
        }
    }

    fn allocate(capacity: usize) -> *mut u8 {
        // Don't allocate here because `Drop` will not deallocate when `capacity` is 0.

        if T::IS_ZST || capacity == 0 {
            null_mut()
        } else {
            let (layout, _) = Self::get_layout(capacity);
            if !alloc_guard(layout.size()) {
                panic!("capacity overflow");
            }
            let ptr = unsafe { alloc::alloc::alloc(layout) };
            if ptr.is_null() {
                panic!("allocation failed");
            }
            unsafe {
                ptr.cast::<AllocHeader>().write(AllocHeader {
                    cap: capacity,
                    reserved: UsizeCell::new(0),
                    written: UsizeCell::new(0),
                });
            }

            ptr
        }
    }

    fn reserve_storage(&mut self, num_slots: usize) -> (*mut u8, Range<usize>) {
        let mut current_mem = self.ptr.read();
        if current_mem.is_null() {
            current_mem = self.grow_amortized(0, 0, num_slots).expect("alloc failed");
        }
        let reserved_range = loop {
            let header = NonNull::new(current_mem.cast::<AllocHeader>());
            // SAFETY: we have &mut self
            if let Some(reserved_range) = unsafe { Self::reserve_slots_nonsync(header, num_slots) }
            {
                break reserved_range;
            } else {
                let mut cap = 0;
                let mut len = 0;
                if let Some(header) = header {
                    let header = unsafe { header.as_ref() };
                    cap = header.cap;
                    len = unsafe { header.reserved.read_nonsync() }; // SAFETY: we have &mut self
                }
                current_mem = self
                    .grow_amortized(cap, len, num_slots)
                    .expect("alloc failed");
            }
        };
        (current_mem, reserved_range)
    }

    /// # Safety
    /// NS. The returned range must be written and then marked with
    /// [`mark_range_written_nonsync`](Self::mark_range_written_nonsync) before anything else
    /// touches the vector.
    unsafe fn reserve_storage_nonsync(&self, num_slots: usize) -> (*mut u8, Range<usize>) {
        let mut current_mem = self.ptr.read_nonsync();
        if current_mem.is_null() {
            current_mem = self
                .grow_amortized_nonsync(0, 0, num_slots)
                .expect("alloc failed");
        }
        let reserved_range = loop {
            let header = NonNull::new(current_mem.cast::<AllocHeader>());
            if let Some(reserved_range) = Self::reserve_slots_nonsync(header, num_slots) {
                break reserved_range;
            } else {
                let mut cap = 0;
                let mut len = 0;
                if let Some(header) = header {
                    let header = unsafe { header.as_ref() };
                    cap = header.cap;
                    len = header.reserved.read_nonsync();
                }
                current_mem = self
                    .grow_amortized_nonsync(cap, len, num_slots)
                    .expect("alloc failed");
            }
        };
        (current_mem, reserved_range)
    }

    /// # Safety
    /// NS; `storage` is the allocation `range` was reserved in, and its slots are written.
    #[inline(always)]
    unsafe fn mark_range_written_nonsync(&self, storage: *mut u8, range: Range<usize>) {
        let header = &*storage.cast::<AllocHeader>();
        header.written.write_nonsync(range.end);
    }

    pub fn pop(&mut self) -> Option<T> {
        if let Some((data, mut header)) = unsafe { self.current_memory_nonsync() } {
            unsafe {
                let header = header.as_mut();
                debug_assert!(header.written.read() == header.reserved.read());
                let len = header.written.read_nonsync();
                if len == 0 {
                    return None;
                }
                let new_len = len - 1;
                header.written.set(new_len);
                header.reserved.set(new_len);
                Some(data.as_ptr().add(new_len).read())
            }
        } else {
            None
        }
    }

    /// Remove and return the last element.
    ///
    /// # Safety
    /// NS. No live `&T` into the last element, nor a `&[T]` (from `Deref`) spanning it.
    pub unsafe fn pop_nonsync(&self) -> Option<T> {
        if let Some((data, mut header)) = unsafe { self.current_memory_nonsync() } {
            unsafe {
                let header = header.as_mut();
                debug_assert!(header.written.read() == header.reserved.read());
                let len = header.written.read_nonsync();
                if len == 0 {
                    return None;
                }
                let new_len = len - 1;
                header.written.write_nonsync(new_len);
                header.reserved.write_nonsync(new_len);
                Some(data.as_ptr().add(new_len).read())
            }
        } else {
            None
        }
    }

    pub fn push(&mut self, value: T) {
        let (ptr, reserved_range) = self.reserve_storage(1);
        debug_assert!(reserved_range.len() == 1);
        unsafe {
            let data = ptr
                .add(self.data_start)
                .cast::<T>()
                .add(reserved_range.start);
            core::ptr::write(data, value);
            self.mark_range_written_nonsync(ptr, reserved_range);
        }
    }

    pub fn clean_old_allocs(&mut self) {
        let old_allocs = self.old_allocs.get_mut().expect("lock poisoned");
        for ptr in old_allocs.drain(0..old_allocs.len()) {
            let header = unsafe { &mut *ptr.cast::<AllocHeader>() };
            let len = header.written.read();
            let data_ptr = unsafe { ptr.add(self.data_start) };
            let (layout, _) = Self::get_layout(header.cap);
            unsafe {
                core::ptr::drop_in_place(core::slice::from_raw_parts_mut(data_ptr, len));
                alloc::alloc::dealloc(ptr, layout)
            };
        }
    }

    /// Append `value`.
    ///
    /// # Safety
    /// NS. A push that grows the vector clones the elements into a new allocation and leaves the
    /// old one allocated (it is never freed, so outstanding `&T`/`&[T]` stay valid, but they no
    /// longer see later writes).
    pub unsafe fn push_nonsync(&self, value: T) {
        let (ptr, reserved_range) = self.reserve_storage_nonsync(1);
        unsafe {
            let data = ptr
                .add(self.data_start)
                .cast::<T>()
                .add(reserved_range.start);
            core::ptr::write(data, value);
            self.mark_range_written_nonsync(ptr, reserved_range);
        }
    }

    pub fn fill(&mut self, value: T) {
        for item in self.iter_mut() {
            *item = value.clone();
        }
    }

    pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
        (&mut **self).iter_mut()
    }

    pub fn iter(&mut self) -> core::slice::Iter<'_, T> {
        (&**self).iter()
    }

    pub fn capacity(&mut self) -> usize {
        if let Some((_, header)) = unsafe { self.current_memory_nonsync() } {
            unsafe { header.as_ref().cap }
        } else {
            0
        }
    }

    pub fn len_sync(&self) -> usize {
        if let Some((_, header)) = self.current_memory_sync() {
            unsafe { header.as_ref().written.load_atomic(Ordering::Acquire) }
        } else {
            0
        }
    }

    /// The number of written elements.
    ///
    /// # Safety
    /// NS: no other thread is growing or shrinking the vector.
    pub unsafe fn len_nonsync(&self) -> usize {
        if let Some((_, header)) = self.current_memory_nonsync() {
            unsafe { header.as_ref().written.load_atomic(Ordering::Acquire) }
        } else {
            0
        }
    }

    /// Extend the vector by `n` values, using the given value.
    pub fn extend_with(&mut self, n: usize, value: T) {
        if T::IS_ZST {
            return;
        }
        let (storage, range) = self.reserve_storage(n);

        unsafe {
            let data = storage.add(self.data_start).cast::<T>();

            for i in range.clone() {
                ptr::write(data.add(i), value.clone());
            }
            self.mark_range_written_nonsync(storage, range);
        }
    }

    /// Extend the vector by `n` values, using the given value.
    ///
    /// # Safety
    /// As [`push_nonsync`](Self::push_nonsync): NS, and a growth leaves outstanding `&T`/`&[T]`
    /// on the old, never-freed allocation.
    pub unsafe fn extend_with_nonsync(&self, n: usize, value: T) {
        if T::IS_ZST {
            return;
        }
        let (storage, range) = unsafe { self.reserve_storage_nonsync(n) };

        unsafe {
            let data = storage.add(self.data_start).cast::<T>();

            for i in range.clone() {
                ptr::write(data.add(i), value.clone());
            }
            self.mark_range_written_nonsync(storage, range);
        }
    }
    pub fn swap_remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                index, len
            );
        }

        unsafe {
            if let Some((data, mut header)) = self.current_memory_nonsync() {
                let header = header.as_mut();
                let len = header.written.read_nonsync();
                if index >= len {
                    assert_failed(index, len);
                }
                // We replace self[index] with the last element. Note that if the
                // bounds check above succeeds there must be a last element (which
                // can be self[index] itself).
                let base_ptr = data.as_ptr();
                let value = ptr::read(base_ptr.add(index));
                ptr::copy(base_ptr.add(len - 1), base_ptr.add(index), 1);
                header.written.write_nonsync(len - 1);
                header.reserved.write_nonsync(len - 1);
                value
            } else {
                assert_failed(index, 0);
            }
        }
    }

    pub fn clear(&mut self) {
        // SAFETY: we have &mut self
        if let Some((data, mut header)) = unsafe { self.current_memory_nonsync() } {
            unsafe {
                let num_elmts = header.as_ref().written.read_nonsync();
                header.as_mut().written.write_nonsync(0);
                header.as_mut().reserved.write_nonsync(0);
                for i in 0..num_elmts {
                    core::ptr::drop_in_place(data.as_ptr().add(i));
                }
            }
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        unsafe {
            if let Some((_, header)) = self.current_memory_nonsync() {
                let header = header.as_ref();
                let cap = header.cap;
                let len = header.reserved.read_nonsync();
                self.grow_amortized(cap, len, additional)
                    .expect("alloc failed");
            } else {
                self.grow_amortized(0, 0, additional).expect("alloc failed");
            }
        }
    }
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let mut iterator = iter.into_iter();
        while let Some(element) = iterator.next() {
            unsafe {
                if let Some((_, header)) = self.current_memory_nonsync() {
                    let header = header.as_ref();
                    if header.cap == header.reserved.read_nonsync() {
                        let (lower, _) = iterator.size_hint();
                        self.reserve(lower.saturating_add(1));
                    }
                } else {
                    let (lower, _) = iterator.size_hint();
                    self.grow_amortized(0, 0, lower.saturating_add(1))
                        .expect("alloc failed");
                }
                let (data, mut header) = self.current_memory_nonsync().unwrap();
                let header = header.as_mut();
                let curr = header.reserved.read_nonsync();
                ptr::write(data.as_ptr().add(curr), element);
                header.reserved.write_nonsync(curr + 1);
                assert!(header.written.read_nonsync() == curr);
                header.written.write_nonsync(curr + 1);
            }
        }
    }

    pub fn resize(&mut self, new_len: usize, value: T) {
        let len = unsafe { self.len_nonsync() };

        if new_len > len {
            // SAFETY: we have &mut self
            unsafe { self.extend_with_nonsync(new_len - len, value) }
        } else {
            self.truncate(new_len);
        }
    }

    pub fn truncate(&mut self, len: usize) {
        // SAFETY: we have &mut self
        unsafe { self.truncate_nonsync(len) }
    }

    /// Shorten the vector to `len` elements, dropping the rest. No-op if it is not longer.
    ///
    /// # Safety
    /// NS. No live `&T` into the dropped elements, nor a `&[T]` (from `Deref`) spanning them.
    pub unsafe fn truncate_nonsync(&self, len: usize) {
        if let Some((data, header)) = self.current_memory_nonsync() {
            // Only `&AllocHeader`: its counters are cells.
            let header = header.as_ref();
            let old_len = header.written.read_nonsync();
            if len >= old_len {
                return;
            }
            header.reserved.write_nonsync(len);
            header.written.write_nonsync(len);
            let s = ptr::slice_from_raw_parts_mut(data.as_ptr().add(len), old_len - len);
            ptr::drop_in_place(s);
        }
    }

    /// Pointer to the first element, with write permission for every written element (taken
    /// from the allocation, not from a `Deref` slice). Dangling when nothing is allocated.
    ///
    /// # Safety
    /// NS. The pointer is valid until the vector next grows, shrinks or drops. Writing
    /// through it requires that no `&T`, or `&[T]` from `Deref`, overlapping the written
    /// elements is live.
    pub unsafe fn as_mut_ptr_nonsync(&self) -> *mut T {
        match self.current_memory_nonsync() {
            Some((data, _)) => data.as_ptr(),
            None => NonNull::dangling().as_ptr(),
        }
    }

    /// Overwrite element `idx` (dropping the old value). Panics if `idx` is out of bounds.
    ///
    /// # Safety
    /// NS. No live `&T` into element `idx`, nor a `&[T]` (from `Deref`) spanning it.
    pub unsafe fn set_nonsync(&self, idx: usize, value: T) {
        let len = self.len_nonsync();
        assert!(idx < len, "set_nonsync index (is {}) should be < len (is {})", idx, len);
        *self.as_mut_ptr_nonsync().add(idx) = value;
    }
}

fn alloc_guard(alloc_size: usize) -> bool {
    if usize::BITS < 64 && alloc_size > isize::MAX as usize {
        false
    } else {
        true
    }
}

// impl<T: Clone, I: SliceIndex<[T]>> Index<I> for KVec<T> {
//     type Output = I::Output;

//     #[inline]
//     fn index(&self, index: I) -> &Self::Output {
//         Index::index(&**self, index)
//     }
// }

// impl<T: Clone, I: SliceIndex<[T]>> IndexMut<I> for KVec<T> {
//     #[inline]
//     fn index_mut(&mut self, index: I) -> &mut Self::Output {
//         IndexMut::index_mut(&mut **self, index)
//     }
// }

impl<T: Clone> ops::Deref for KVec<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        if let Some((data, header)) = self.current_memory_sync() {
            unsafe {
                core::slice::from_raw_parts(
                    data.as_ptr(),
                    header.as_ref().written.load_atomic(Ordering::Acquire),
                )
            }
        } else {
            &[]
        }
    }
}

impl<T: Clone> ops::DerefMut for KVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFETY: we have &mut self
        if let Some((data, mut header)) = unsafe { self.current_memory_nonsync() } {
            unsafe {
                core::slice::from_raw_parts_mut(data.as_ptr(), header.as_mut().written.read())
            }
        } else {
            &mut []
        }
    }
}
