use core::ptr::drop_in_place;

use alloc::vec::Vec;

use crate::{entities::Entities, Archetype, DynamicBundle, Entity, TypeInfo};

/// An entity removed from a `World`
pub struct TakenEntity<'a> {
    entities: &'a mut Entities,
    entity: Entity,
    archetype: &'a mut Archetype,
    index: u32,
    drop: bool,
    /// Hold the ID instead of freeing it (a quarantining archetype).
    hold: bool,
}

impl<'a> TakenEntity<'a> {
    /// # Safety
    /// `index` must be in bounds in `archetype`
    pub(crate) unsafe fn new(
        entities: &'a mut Entities,
        entity: Entity,
        archetype: &'a mut Archetype,
        index: u32,
        hold: bool,
    ) -> Self {
        Self {
            entities,
            entity,
            archetype,
            index,
            drop: true,
            hold,
        }
    }

    fn retire(&mut self) {
        if self.hold {
            unsafe { self.entities.hold_nonsync(self.entity).unwrap() };
        } else {
            self.entities.free(self.entity).unwrap();
        }
    }
}

unsafe impl<'a> DynamicBundle for TakenEntity<'a> {
    fn with_ids<T>(&self, f: impl FnOnce(&[crate::StableTypeId]) -> T) -> T {
        f(self.archetype.type_ids())
    }

    fn type_info(&self) -> Vec<crate::TypeInfo> {
        self.archetype.types().to_vec()
    }

    unsafe fn put(mut self, mut f: impl FnMut(*mut u8, TypeInfo)) {
        // Suppress dropping of moved components
        self.drop = false;
        self.retire();
        for ty in self.archetype.types() {
            let mut ptr = self.archetype.get_dynamic(ty, self.index).unwrap();
            ptr.move_value_and_tombstone(ty, &mut f);
        }
        self.archetype.set_entity_free(self.index as usize);
    }
}

impl Drop for TakenEntity<'_> {
    fn drop(&mut self) {
        if self.drop {
            self.retire();
            for ty in self.archetype.types() {
                unsafe {
                    let mut ptr = self.archetype.get_dynamic(ty, self.index).unwrap();
                    ptr.drop_value_and_tombstone(ty);
                }
            }
            self.archetype.set_entity_free(self.index as usize);
        }
    }
}
