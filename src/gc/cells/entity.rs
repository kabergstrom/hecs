use core::{
    cell::UnsafeCell,
    num::NonZeroU32,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::Entity;

/// A cell holding an [`Entity`] packed as `(generation << 32) | id`,
/// matching [`Entity::to_bits`]. Supports synchronized atomic access via
/// `AtomicU64` and unsynchronized direct access.
///
/// A slot whose id field equals `u32::MAX` is treated as free. The packed
/// "free" value used for reset/fill is [`Entity::DANGLING`]'s bit pattern.
#[repr(transparent)]
pub struct EntityCell(UnsafeCell<u64>);
unsafe impl Sync for EntityCell {}
unsafe impl Send for EntityCell {}

const FREE_BITS: u64 = ((u32::MAX as u64) << 32) | (u32::MAX as u64);

#[inline]
fn pack(entity: Entity) -> u64 {
    (u64::from(entity.generation.get()) << 32) | u64::from(entity.id)
}

#[inline]
fn unpack(bits: u64) -> Entity {
    Entity {
        id: bits as u32,
        // SAFETY: any value stored via EntityCell either came from a real
        // Entity (whose generation is NonZeroU32) or is the FREE_BITS
        // pattern where the generation field is u32::MAX, which is non-zero.
        generation: unsafe { NonZeroU32::new_unchecked((bits >> 32) as u32) },
    }
}

impl EntityCell {
    pub fn new(entity: Entity) -> Self {
        Self(UnsafeCell::new(pack(entity)))
    }
    pub fn free() -> Self {
        Self(UnsafeCell::new(FREE_BITS))
    }
    pub fn write_atomic(&self, entity: Entity, ordering: Ordering) {
        unsafe { (&*self.0.get().cast::<AtomicU64>()).store(pack(entity), ordering) }
    }
    pub fn load_atomic(&self, ordering: Ordering) -> Entity {
        let bits = unsafe { (&*self.0.get().cast::<AtomicU64>()).load(ordering) };
        unpack(bits)
    }
    pub fn load_atomic_bits(&self, ordering: Ordering) -> u64 {
        unsafe { (&*self.0.get().cast::<AtomicU64>()).load(ordering) }
    }
    pub fn store_free_atomic(&self, ordering: Ordering) {
        unsafe { (&*self.0.get().cast::<AtomicU64>()).store(FREE_BITS, ordering) }
    }
    pub unsafe fn write_nonsync(&self, entity: Entity) {
        self.0.get().write(pack(entity))
    }
    pub unsafe fn write_free_nonsync(&self) {
        self.0.get().write(FREE_BITS)
    }
    pub unsafe fn read_nonsync(&self) -> Entity {
        unpack(*self.0.get())
    }
    pub unsafe fn read_id_nonsync(&self) -> u32 {
        *self.0.get() as u32
    }
    pub fn read(&mut self) -> Entity {
        unsafe { unpack(*self.0.get()) }
    }
    pub fn read_id(&mut self) -> u32 {
        unsafe { *self.0.get() as u32 }
    }
    pub fn set(&mut self, entity: Entity) {
        *self.0.get_mut() = pack(entity);
    }
    pub fn set_free(&mut self) {
        *self.0.get_mut() = FREE_BITS;
    }
    /// Returns true if the slot is unoccupied (id == u32::MAX).
    pub fn is_free_atomic(&self, ordering: Ordering) -> bool {
        (self.load_atomic_bits(ordering) as u32) == u32::MAX
    }
}

impl Default for EntityCell {
    fn default() -> Self {
        Self::free()
    }
}

impl Clone for EntityCell {
    fn clone(&self) -> Self {
        Self(UnsafeCell::new(self.load_atomic_bits(Ordering::Relaxed)))
    }
}

impl From<Entity> for EntityCell {
    fn from(v: Entity) -> Self {
        Self::new(v)
    }
}
