use core::{
    cell::UnsafeCell,
    sync::atomic::{AtomicIsize, Ordering},
};

#[repr(transparent)]
#[derive(Default)]
pub struct IsizeCell(UnsafeCell<isize>);
// SAFETY: the safe `&self` methods are atomic (the value is accessed as the matching atomic,
// which has the same layout); the `*_nonsync` methods are `unsafe` with an NS contract. The
// `Into` impl for `&Self` (where there is one) is a plain read: it is crate-internal and only
// used under NS. Cross-thread use beyond the atomics relies on the engine's invariant that the
// `World` is only touched from its owning thread (see the `Send` impl of `gc::GCPtr`).
unsafe impl Sync for IsizeCell {}
unsafe impl Send for IsizeCell {}

impl IsizeCell {
    pub fn new(val: isize) -> Self {
        Self(UnsafeCell::new(val))
    }
    pub fn write_atomic(&self, val: isize, ordering: Ordering) {
        unsafe { (&*self.0.get().cast::<AtomicIsize>()).store(val, ordering) }
    }
    pub fn load_atomic(&self, ordering: Ordering) -> isize {
        unsafe { (&*self.0.get().cast::<AtomicIsize>()).load(ordering) }
    }
    pub fn fetch_sub(&self, val: isize, ordering: Ordering) -> isize {
        unsafe { (&*self.0.get().cast::<AtomicIsize>()).fetch_sub(val, ordering) }
    }
    /// Plain (non-atomic) write.
    ///
    /// # Safety
    /// NS: no other thread reads or writes this cell concurrently.
    pub unsafe fn write_nonsync(&self, val: isize) {
        self.0.get().write(val)
    }
    /// Plain (non-atomic) read.
    ///
    /// # Safety
    /// NS: no other thread writes this cell concurrently.
    pub unsafe fn read_nonsync(&self) -> isize {
        unsafe { *self.0.get() }
    }
    pub fn read(&mut self) -> isize {
        unsafe { *self.0.get() }
    }
    pub fn set(&mut self, val: isize) {
        *self.0.get_mut() = val;
    }

    pub fn compare_exchange_weak(
        &self,
        current: isize,
        new: isize,
        success: Ordering,
        failure: Ordering,
    ) -> Result<isize, isize> {
        unsafe {
            (&*self.0.get().cast::<AtomicIsize>())
                .compare_exchange_weak(current, new, success, failure)
        }
    }
}
impl Clone for IsizeCell {
    fn clone(&self) -> Self {
        Self(UnsafeCell::new(self.load_atomic(Ordering::Relaxed)))
    }
}

impl From<isize> for IsizeCell {
    fn from(v: isize) -> Self {
        Self(UnsafeCell::new(v))
    }
}

impl Into<isize> for &IsizeCell {
    fn into(self) -> isize {
        unsafe { *self.0.get() }
    }
}
