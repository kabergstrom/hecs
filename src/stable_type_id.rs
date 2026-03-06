/// A stable, cross-cdylib type identifier.
///
/// Unlike `std::any::TypeId`, this is a FNV-1a hash of the type's qualified
/// name, computed as a `const` expression via `#[derive(Component)]`.
/// Identical source → identical hash, even across separately compiled cdylibs.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct StableTypeId(pub u64);

impl StableTypeId {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x0100000001b3;

    /// Compute FNV-1a hash of `bytes` at compile time.
    pub const fn fnv1a(bytes: &[u8]) -> u64 {
        let mut hash = Self::FNV_OFFSET;
        let mut i = 0;
        while i < bytes.len() {
            hash ^= bytes[i] as u64;
            hash = hash.wrapping_mul(Self::FNV_PRIME);
            i += 1;
        }
        hash
    }
}

impl core::fmt::Debug for StableTypeId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "StableTypeId({:#018x})", self.0)
    }
}
