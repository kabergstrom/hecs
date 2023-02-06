use core::{
    cell::UnsafeCell,
    sync::atomic::{AtomicUsize, Ordering},
};

#[repr(transparent)]
#[derive(Default)]
pub struct UsizeCell(UnsafeCell<usize>);

impl UsizeCell {
    pub fn new(val: usize) -> Self {
        Self(UnsafeCell::new(val))
    }
    pub fn write_atomic(&self, val: usize, ordering: Ordering) {
        unsafe { (&*self.0.get().cast::<AtomicUsize>()).store(val, ordering) }
    }
    pub fn load_atomic(&self, ordering: Ordering) -> usize {
        unsafe { (&*self.0.get().cast::<AtomicUsize>()).load(ordering) }
    }
    pub unsafe fn write_nonsync(&self, val: usize) {
        self.0.get().write(val)
    }
    pub unsafe fn read_nonsync(&self) -> usize {
        unsafe { *self.0.get() }
    }
    pub fn read(&mut self) -> usize {
        unsafe { *self.0.get() }
    }
    pub fn set(&mut self, val: usize) {
        *self.0.get_mut() = val;
    }

    pub fn compare_exchange_weak(
        &self,
        current: usize,
        new: usize,
        success: Ordering,
        failure: Ordering,
    ) -> Result<usize, usize> {
        unsafe {
            (&*self.0.get().cast::<AtomicUsize>())
                .compare_exchange_weak(current, new, success, failure)
        }
    }
}
impl Clone for UsizeCell {
    fn clone(&self) -> Self {
        Self(UnsafeCell::new(self.load_atomic(Ordering::Relaxed)))
    }
}

impl From<usize> for UsizeCell {
    fn from(v: usize) -> Self {
        Self(UnsafeCell::new(v))
    }
}

impl Into<usize> for &UsizeCell {
    fn into(self) -> usize {
        unsafe { *self.0.get() }
    }
}
