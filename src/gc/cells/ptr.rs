use core::{
    cell::UnsafeCell,
    sync::atomic::{AtomicPtr, Ordering},
};

#[repr(transparent)]
pub struct PtrCell<T>(UnsafeCell<*mut T>);
unsafe impl<T> Sync for PtrCell<T> {}
unsafe impl<T> Send for PtrCell<T> {}

impl<T> PtrCell<T> {
    pub fn new(val: *mut T) -> Self {
        Self(UnsafeCell::new(val))
    }
    pub fn write_atomic(&self, val: *mut T, ordering: Ordering) {
        unsafe { (&*self.0.get().cast::<AtomicPtr<T>>()).store(val, ordering) }
    }
    pub fn load_atomic(&self, ordering: Ordering) -> *mut T {
        unsafe { (&*self.0.get().cast::<AtomicPtr<T>>()).load(ordering) }
    }
    pub unsafe fn write_nonsync(&self, val: *mut T) {
        self.0.get().write(val)
    }
    pub unsafe fn read_nonsync(&self) -> *mut T {
        unsafe { *self.0.get() }
    }
    pub fn read(&mut self) -> *mut T {
        unsafe { *self.0.get() }
    }
    pub fn set(&mut self, val: *mut T) {
        *self.0.get_mut() = val;
    }

    pub fn compare_exchange_weak(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        unsafe {
            (&*self.0.get().cast::<AtomicPtr<T>>())
                .compare_exchange_weak(current, new, success, failure)
        }
    }
}
impl<T> Clone for PtrCell<T> {
    fn clone(&self) -> Self {
        Self(UnsafeCell::new(self.load_atomic(Ordering::Relaxed)))
    }
}

impl<T> From<*mut T> for PtrCell<T> {
    fn from(v: *mut T) -> Self {
        Self(UnsafeCell::new(v))
    }
}

impl<T> Into<*mut T> for &PtrCell<T> {
    fn into(self) -> *mut T {
        unsafe { *self.0.get() }
    }
}
