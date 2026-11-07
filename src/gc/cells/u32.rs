use core::{
    cell::UnsafeCell,
    sync::atomic::{AtomicU32, Ordering},
};

#[repr(transparent)]
#[derive(Default)]
pub struct U32Cell(UnsafeCell<u32>);
// SAFETY: the safe `&self` methods are atomic (the value is accessed as the matching atomic,
// which has the same layout); the `*_nonsync` methods are `unsafe` with an NS contract. The
// `Into` impl for `&Self` (where there is one) is a plain read: it is crate-internal and only
// used under NS. Cross-thread use beyond the atomics relies on the engine's invariant that the
// `World` is only touched from its owning thread (see the `Send` impl of `gc::GCPtr`).
unsafe impl Sync for U32Cell {}
unsafe impl Send for U32Cell {}

impl U32Cell {
    pub fn new(val: u32) -> Self {
        Self(UnsafeCell::new(val))
    }
    pub fn write_atomic(&self, val: u32, ordering: Ordering) {
        unsafe { (&*self.0.get().cast::<AtomicU32>()).store(val, ordering) }
    }
    pub fn load_atomic(&self, ordering: Ordering) -> u32 {
        unsafe { (&*self.0.get().cast::<AtomicU32>()).load(ordering) }
    }
    /// Plain (non-atomic) write.
    ///
    /// # Safety
    /// NS: no other thread reads or writes this cell concurrently.
    pub unsafe fn write_nonsync(&self, val: u32) {
        self.0.get().write(val)
    }
    /// Plain (non-atomic) read.
    ///
    /// # Safety
    /// NS: no other thread writes this cell concurrently.
    pub unsafe fn read_nonsync(&self) -> u32 {
        unsafe { *self.0.get() }
    }
    pub fn read(&mut self) -> u32 {
        unsafe { *self.0.get() }
    }
    pub fn set(&mut self, val: u32) {
        *self.0.get_mut() = val;
    }
}
impl Clone for U32Cell {
    fn clone(&self) -> Self {
        Self(UnsafeCell::new(self.load_atomic(Ordering::Relaxed)))
    }
}

impl From<u32> for U32Cell {
    fn from(v: u32) -> Self {
        Self(UnsafeCell::new(v))
    }
}

impl Into<u32> for &U32Cell {
    fn into(self) -> u32 {
        unsafe { *self.0.get() }
    }
}
