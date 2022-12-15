use core::{mem::MaybeUninit, ptr::NonNull};

use crate::{Component, TypeInfo};

pub struct GCPtr {
    pub value: NonNull<u8>,
}
impl GCPtr {
    pub fn header_ptr(&self) -> NonNull<GCHeader> {
        unsafe {
            assert!(
                self.value.as_ptr().sub(core::mem::size_of::<GCHeader>()) as usize
                    % (core::alloc::Layout::new::<GCHeader>().align())
                    == 0
            );
            NonNull::new_unchecked(
                self.value
                    .as_ptr()
                    .sub(core::mem::size_of::<GCHeader>())
                    .cast(),
            )
        }
    }
    pub fn value_ptr(&self) -> NonNull<u8> {
        self.value
    }
    pub unsafe fn drop(&self, ty: &TypeInfo) {
        self.header_ptr().as_ptr().drop_in_place();
        ty.drop_value(self.value_ptr().as_ptr());
    }
    pub unsafe fn from_base(ty: &TypeInfo, base: NonNull<u8>) -> Self {
        Self {
            value: NonNull::new_unchecked(base.as_ptr().add(ty.data_start())),
        }
    }
}

enum State {
    Alive { borrow: i16 },
    Moved { new_ptr: GCPtr },
    Dead,
}
// GCHeader is stored tightly packed before the value in memory.
// When the alignment requirements of the value is larger than the size of GCHeader,
// bytes up to the value address minus the size of GCHeader are unused.
#[repr(C)]
pub struct GCHeader {
    state: State,
}
impl GCHeader {
    pub fn new_alive() -> Self {
        Self {
            state: State::Alive { borrow: 0 },
        }
    }
}
impl<T: Component + core::fmt::Debug> core::fmt::Debug for GC<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

#[repr(C)]
pub struct GC<T> {
    pub header_storage: MaybeUninit<GCHeader>,
    pub value: T,
}
