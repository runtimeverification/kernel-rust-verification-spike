// SPDX-License-Identifier: GPL-2.0
//
// UNION-FREE RE-MODELLING of the Binder BinderObject deserializer.
//
// Derived from the Linux kernel, drivers/android/binder/allocation.rs (v7.2-rc2),
// via ../src/lib.rs (the faithful extraction) and ../reduced/src/lib.rs. See
// REMODEL-REPORT.md. Purpose: Aeneas rejects `union` types, so the union-based
// deserializer core never reaches Lean. Here `BinderObject` is re-modelled as a
// fixed byte array `[u8; 40]` with typed accessor functions that read fields at
// fixed offsets — no union, no MaybeUninit, no raw-pointer cast — so the *whole*
// parse path (read_from / read_from_inner / accessors / parse_one) translates and
// a no-panic theorem on parse_one becomes reachable.
//
// Design agreed with the Aeneas authors in
//   https://github.com/AeneasVerif/aeneas/issues/1199
//
// The parsing control flow is kept identical to the kernel original. Every
// intentional deviation is marked `// REMODEL: <reason>`. Fidelity to the real
// #[repr(C)] layout is pinned by compile-time `offset_of!`/`size_of` assertions
// (below) and, in the tests, by comparison against the *actual union* structs.

use core::mem::size_of;

// --- error handling: identical to ../src/lib.rs ----------------------------
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error(pub i32);
pub const EINVAL: Error = Error(22);
pub const ENOMEM: Error = Error(12);
pub type Result<T = ()> = core::result::Result<T, Error>;

// --- uapi struct layouts ---------------------------------------------------
// REMODEL: the anonymous `union { u64; u32 }` fields of the kernel structs are
// written here as a plain `u64` (their largest member; #[repr(C)] size and
// alignment are identical on a 64-bit target). Keeping a real `union` in the
// crate would make Aeneas abort. These structs exist so `type_to_size` can take
// their `size_of`, and so the compile-time offset assertions below can pin every
// accessor offset to `offset_of!` of the corresponding field. The `#[cfg(test)]`
// module additionally checks these offsets/sizes against the *real union*
// structs, closing the gap to the true kernel layout.
pub mod uapi {
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_object_header {
        pub type_: u32,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct flat_binder_object {
        pub hdr: binder_object_header,
        pub flags: u32,
        pub __bindgen_anon_1: u64, // REMODEL: union { binder: u64, handle: u32 }
        pub cookie: u64,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_fd_object {
        pub hdr: binder_object_header,
        pub pad_flags: u32,
        pub __bindgen_anon_1: u64, // REMODEL: union { pad_binder: u64, fd: u32 }
        pub cookie: u64,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_buffer_object {
        pub hdr: binder_object_header,
        pub flags: u32,
        pub buffer: u64,
        pub length: u64,
        pub parent: u64,
        pub parent_offset: u64,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_fd_array_object {
        pub hdr: binder_object_header,
        pub pad: u32,
        pub num_fds: u64,
        pub parent: u64,
        pub parent_offset: u64,
    }
}

// --- BINDER_TYPE_* constants: identical to ../src/lib.rs --------------------
pub const BINDER_TYPE_BINDER: u32 = 0x73622a85;
pub const BINDER_TYPE_WEAK_BINDER: u32 = 0x77622a85;
pub const BINDER_TYPE_HANDLE: u32 = 0x73682a85;
pub const BINDER_TYPE_WEAK_HANDLE: u32 = 0x77682a85;
pub const BINDER_TYPE_FD: u32 = 0x66642a85;
pub const BINDER_TYPE_FDA: u32 = 0x66646185;
pub const BINDER_TYPE_PTR: u32 = 0x70742a85;

// --- type_to_size / validators: byte-for-byte from ../src/lib.rs ------------
pub fn type_to_size(type_: u32) -> Option<usize> {
    match type_ {
        BINDER_TYPE_WEAK_BINDER => Some(size_of::<uapi::flat_binder_object>()),
        BINDER_TYPE_BINDER => Some(size_of::<uapi::flat_binder_object>()),
        BINDER_TYPE_WEAK_HANDLE => Some(size_of::<uapi::flat_binder_object>()),
        BINDER_TYPE_HANDLE => Some(size_of::<uapi::flat_binder_object>()),
        BINDER_TYPE_FD => Some(size_of::<uapi::binder_fd_object>()),
        BINDER_TYPE_PTR => Some(size_of::<uapi::binder_buffer_object>()),
        BINDER_TYPE_FDA => Some(size_of::<uapi::binder_fd_array_object>()),
        _ => None,
    }
}

pub fn ptr_align(value: usize) -> Option<usize> {
    let size = core::mem::size_of::<usize>() - 1;
    Some(value.checked_add(size)? & !size)
}

pub fn is_aligned(value: usize, to: usize) -> bool {
    value % to == 0
}

pub fn size_check(offset: usize, size: usize, buffer_size: usize) -> Result {
    let overflow_fail = offset.checked_add(size).is_none();
    let cmp_size_fail = offset.wrapping_add(size) > buffer_size;
    if overflow_fail || cmp_size_fail {
        return Err(EINVAL);
    }
    Ok(())
}

// --- byte-source reader: identical to ../src/lib.rs (already union-free) -----
pub struct SliceReader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> SliceReader<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        SliceReader { data, pos: 0 }
    }

    fn len(&self) -> usize {
        self.data.len() - self.pos
    }

    fn clone_reader(&self) -> SliceReader<'a> {
        SliceReader {
            data: self.data,
            pos: self.pos,
        }
    }

    fn read_slice(&mut self, out: &mut [u8]) -> Result {
        let n = out.len();
        if n > self.len() {
            return Err(EINVAL);
        }
        out.copy_from_slice(&self.data[self.pos..self.pos + n]);
        self.pos += n;
        Ok(())
    }

    fn skip(&mut self, n: usize) -> Result {
        if n > self.len() {
            return Err(EINVAL);
        }
        self.pos += n;
        Ok(())
    }
}

// ===========================================================================
// The union-free BinderObject.
//
// REMODEL: the kernel's `union BinderObject { hdr, fbo, fdo, bbo, fdao }` becomes
// a fixed byte array. Its size is the largest variant (binder_buffer_object, 40
// bytes) — exactly `size_of::<BinderObject>()` in the original.
// ===========================================================================

/// REMODEL: `size_of::<BinderObject>()` in the kernel; pinned to the real layout
/// by the `size_of` assertions below.
pub const OBJECT_SIZE: usize = 40;

/// A binder object as it is serialized, as raw bytes.
///
/// # Invariants (as in the kernel original)
/// All bytes are initialized, and `hdr_type()` is one of the allowed types.
pub struct BinderObjectBytes(pub [u8; OBJECT_SIZE]);

// REMODEL: little-endian field reads at fixed, literal offsets replace the C
// union field accesses. Literal indices keep every read trivially in-bounds
// (< OBJECT_SIZE), and `from_le_bytes` is a total decode.
macro_rules! rd_u32 {
    ($s:expr; $a:literal, $b:literal, $c:literal, $d:literal) => {
        u32::from_le_bytes([$s.0[$a], $s.0[$b], $s.0[$c], $s.0[$d]])
    };
}
macro_rules! rd_u64 {
    ($s:expr; $a:literal, $b:literal, $c:literal, $d:literal,
              $e:literal, $f:literal, $g:literal, $h:literal) => {
        u64::from_le_bytes([
            $s.0[$a], $s.0[$b], $s.0[$c], $s.0[$d],
            $s.0[$e], $s.0[$f], $s.0[$g], $s.0[$h],
        ])
    };
}

impl BinderObjectBytes {
    pub fn read_from(reader: &mut SliceReader) -> Result<BinderObjectBytes> {
        let object = Self::read_from_inner(|mut slice| {
            let read_len = usize::min(slice.len(), reader.len());
            reader.clone_reader().read_slice(&mut slice[..read_len])?;
            Ok(slice)
        })?;

        // Same as the kernel: advance the caller's reader by the object's size.
        // `skip` fails (EINVAL) if the tag's size exceeds the remaining input.
        reader.skip(object.size())?;

        Ok(object)
    }

    /// Use the provided reader closure to construct a `BinderObjectBytes`.
    pub fn read_from_inner<R>(fill: R) -> Result<BinderObjectBytes>
    where
        // REMODEL: the kernel closure is `FnOnce(&mut [u8; N]) -> Result<()>`,
        // filling a caller-provided buffer in place. Aeneas cannot thread the
        // `&mut [u8; N]` write-back through a *generic* `FnOnce` (the trait's
        // `call_once` return type does not carry the mutated buffer), so here the
        // closure takes the (zeroed) buffer by value and returns it filled. Same
        // fill-then-validate protocol and control flow; only the buffer-passing
        // convention differs.
        R: FnOnce([u8; OBJECT_SIZE]) -> Result<[u8; OBJECT_SIZE]>,
    {
        // REMODEL: zeroed byte array instead of `MaybeUninit::<BinderObject>::zeroed()`.
        // REMODEL: fill the bytes directly; the kernel casts the
        // `MaybeUninit<BinderObject>` to `&mut [u8; N]` via a raw pointer here.
        let bytes = fill([0u8; OBJECT_SIZE])?;
        let obj = BinderObjectBytes(bytes);

        // REMODEL: read the tag with a typed accessor instead of
        // `unsafe { obj.assume_init_ref().hdr.type_ }`.
        let type_ = obj.hdr_type();
        if type_to_size(type_).is_none() {
            // The value of the type header was invalid.
            return Err(EINVAL);
        }

        // REMODEL: the validated bytes *are* the object; no `assume_init`.
        Ok(obj)
    }

    pub fn size(&self) -> usize {
        // REMODEL: the kernel is `type_to_size(self.hdr.type_).unwrap_unchecked()`,
        // relying on the type invariant. We keep this TOTAL: an invalid tag —
        // impossible for a value produced by `read_from_inner`, which validated
        // it — maps to 0 rather than triggering UB / a panic. The return value is
        // unchanged for every valid tag.
        match type_to_size(self.hdr_type()) {
            Some(n) => n,
            None => 0,
        }
    }

    // --- typed accessors: REMODEL of `as_ref` -------------------------------
    // The kernel's `as_ref` matches the tag and returns a `&mut` typed view into
    // the union. Here each field is read explicitly at its offset. Offsets are
    // pinned to `offset_of!` of the corresponding struct field by the compile-time
    // assertions below.

    /// `hdr.type_` — offset 0.
    pub fn hdr_type(&self) -> u32 {
        rd_u32!(self; 0, 1, 2, 3)
    }

    // flat_binder_object (tags BINDER / WEAK_BINDER / HANDLE / WEAK_HANDLE)
    pub fn fbo_flags(&self) -> u32 {
        rd_u32!(self; 4, 5, 6, 7)
    }
    /// The `binder` interpretation of the anon union (offset 8, u64).
    pub fn fbo_binder(&self) -> u64 {
        rd_u64!(self; 8, 9, 10, 11, 12, 13, 14, 15)
    }
    /// The `handle` interpretation of the anon union (offset 8, low u32).
    pub fn fbo_handle(&self) -> u32 {
        rd_u32!(self; 8, 9, 10, 11)
    }
    pub fn fbo_cookie(&self) -> u64 {
        rd_u64!(self; 16, 17, 18, 19, 20, 21, 22, 23)
    }

    // binder_fd_object (tag FD)
    /// The `fd` interpretation of the anon union (offset 8, low u32).
    pub fn fdo_fd(&self) -> u32 {
        rd_u32!(self; 8, 9, 10, 11)
    }
    pub fn fdo_cookie(&self) -> u64 {
        rd_u64!(self; 16, 17, 18, 19, 20, 21, 22, 23)
    }

    // binder_buffer_object (tag PTR)
    pub fn bbo_flags(&self) -> u32 {
        rd_u32!(self; 4, 5, 6, 7)
    }
    pub fn bbo_buffer(&self) -> u64 {
        rd_u64!(self; 8, 9, 10, 11, 12, 13, 14, 15)
    }
    pub fn bbo_length(&self) -> u64 {
        rd_u64!(self; 16, 17, 18, 19, 20, 21, 22, 23)
    }
    pub fn bbo_parent(&self) -> u64 {
        rd_u64!(self; 24, 25, 26, 27, 28, 29, 30, 31)
    }
    pub fn bbo_parent_offset(&self) -> u64 {
        rd_u64!(self; 32, 33, 34, 35, 36, 37, 38, 39)
    }

    // binder_fd_array_object (tag FDA)
    pub fn fdao_num_fds(&self) -> u64 {
        rd_u64!(self; 8, 9, 10, 11, 12, 13, 14, 15)
    }
    pub fn fdao_parent(&self) -> u64 {
        rd_u64!(self; 16, 17, 18, 19, 20, 21, 22, 23)
    }
    pub fn fdao_parent_offset(&self) -> u64 {
        rd_u64!(self; 24, 25, 26, 27, 28, 29, 30, 31)
    }
}

/// Same top-level entry point as ../src/lib.rs.
pub fn parse_one(bytes: &[u8]) -> Result<usize> {
    let mut reader = SliceReader::new(bytes);
    let obj = BinderObjectBytes::read_from(&mut reader)?;
    Ok(obj.size())
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::offset_of;

    // ===================================================================
    // Compile-time fidelity assertions: pin every accessor offset to
    // `offset_of!` of the real field, and every size used by `type_to_size` to
    // `size_of`. Kept in `#[cfg(test)]` so Charon (which builds without `--test`)
    // does not extract them: `offset_of!` const-folds to literals and these add
    // nothing to the extracted program. Layout is a property of the types, which
    // are identical in both builds, so checking here pins the extraction too.
    // ===================================================================
    const _: () = {
        // hdr.type_
        assert!(offset_of!(uapi::binder_object_header, type_) == 0);
        // flat_binder_object
        assert!(offset_of!(uapi::flat_binder_object, flags) == 4);
        assert!(offset_of!(uapi::flat_binder_object, __bindgen_anon_1) == 8);
        assert!(offset_of!(uapi::flat_binder_object, cookie) == 16);
        assert!(size_of::<uapi::flat_binder_object>() == 24);
        // binder_fd_object
        assert!(offset_of!(uapi::binder_fd_object, __bindgen_anon_1) == 8);
        assert!(offset_of!(uapi::binder_fd_object, cookie) == 16);
        assert!(size_of::<uapi::binder_fd_object>() == 24);
        // binder_buffer_object
        assert!(offset_of!(uapi::binder_buffer_object, flags) == 4);
        assert!(offset_of!(uapi::binder_buffer_object, buffer) == 8);
        assert!(offset_of!(uapi::binder_buffer_object, length) == 16);
        assert!(offset_of!(uapi::binder_buffer_object, parent) == 24);
        assert!(offset_of!(uapi::binder_buffer_object, parent_offset) == 32);
        assert!(size_of::<uapi::binder_buffer_object>() == 40);
        // binder_fd_array_object
        assert!(offset_of!(uapi::binder_fd_array_object, num_fds) == 8);
        assert!(offset_of!(uapi::binder_fd_array_object, parent) == 16);
        assert!(offset_of!(uapi::binder_fd_array_object, parent_offset) == 24);
        assert!(size_of::<uapi::binder_fd_array_object>() == 32);
        // the byte array is exactly the largest variant, i.e. size_of::<BinderObject>()
        assert!(OBJECT_SIZE == 40);
        assert!(OBJECT_SIZE == size_of::<uapi::binder_buffer_object>());
    };

    // ------------------------------------------------------------------
    // Fidelity to the REAL kernel layout: the actual `union`-bearing structs
    // (as in ../src/lib.rs). Kept in `#[cfg(test)]` only — a real `union` in the
    // extracted crate would make Aeneas abort. This proves the union-free structs
    // used above have byte-identical offsets/sizes to the real ones.
    // ------------------------------------------------------------------
    mod real_uapi {
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub struct binder_object_header {
            pub type_: u32,
        }
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub union flat_binder_object__bindgen_ty_1 {
            pub binder: u64,
            pub handle: u32,
        }
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub struct flat_binder_object {
            pub hdr: binder_object_header,
            pub flags: u32,
            pub __bindgen_anon_1: flat_binder_object__bindgen_ty_1,
            pub cookie: u64,
        }
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub union binder_fd_object__bindgen_ty_1 {
            pub pad_binder: u64,
            pub fd: u32,
        }
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub struct binder_fd_object {
            pub hdr: binder_object_header,
            pub pad_flags: u32,
            pub __bindgen_anon_1: binder_fd_object__bindgen_ty_1,
            pub cookie: u64,
        }
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub struct binder_buffer_object {
            pub hdr: binder_object_header,
            pub flags: u32,
            pub buffer: u64,
            pub length: u64,
            pub parent: u64,
            pub parent_offset: u64,
        }
        #[repr(C)]
        #[derive(Copy, Clone)]
        pub struct binder_fd_array_object {
            pub hdr: binder_object_header,
            pub pad: u32,
            pub num_fds: u64,
            pub parent: u64,
            pub parent_offset: u64,
        }
    }

    // The union-free structs used for extraction match the real union structs,
    // field-offset for field-offset and size for size. Checked at compile time.
    const _: () = {
        assert!(
            offset_of!(uapi::flat_binder_object, __bindgen_anon_1)
                == offset_of!(real_uapi::flat_binder_object, __bindgen_anon_1)
        );
        assert!(
            offset_of!(uapi::flat_binder_object, cookie)
                == offset_of!(real_uapi::flat_binder_object, cookie)
        );
        assert!(size_of::<uapi::flat_binder_object>() == size_of::<real_uapi::flat_binder_object>());
        assert!(
            offset_of!(uapi::binder_fd_object, __bindgen_anon_1)
                == offset_of!(real_uapi::binder_fd_object, __bindgen_anon_1)
        );
        assert!(size_of::<uapi::binder_fd_object>() == size_of::<real_uapi::binder_fd_object>());
        assert!(
            size_of::<uapi::binder_buffer_object>()
                == size_of::<real_uapi::binder_buffer_object>()
        );
        assert!(
            offset_of!(uapi::binder_buffer_object, parent_offset)
                == offset_of!(real_uapi::binder_buffer_object, parent_offset)
        );
        assert!(
            size_of::<uapi::binder_fd_array_object>()
                == size_of::<real_uapi::binder_fd_array_object>()
        );
    };

    // type_to_size returns exactly size_of of the corresponding struct.
    #[test]
    fn type_to_size_matches_sizeof() {
        assert_eq!(type_to_size(BINDER_TYPE_BINDER), Some(size_of::<uapi::flat_binder_object>()));
        assert_eq!(type_to_size(BINDER_TYPE_WEAK_BINDER), Some(size_of::<uapi::flat_binder_object>()));
        assert_eq!(type_to_size(BINDER_TYPE_HANDLE), Some(size_of::<uapi::flat_binder_object>()));
        assert_eq!(type_to_size(BINDER_TYPE_WEAK_HANDLE), Some(size_of::<uapi::flat_binder_object>()));
        assert_eq!(type_to_size(BINDER_TYPE_FD), Some(size_of::<uapi::binder_fd_object>()));
        assert_eq!(type_to_size(BINDER_TYPE_PTR), Some(size_of::<uapi::binder_buffer_object>()));
        assert_eq!(type_to_size(BINDER_TYPE_FDA), Some(size_of::<uapi::binder_fd_array_object>()));
        assert_eq!(type_to_size(0xdead_beef), None);
    }

    // Helper: build a 40-byte object with a given tag and zeroed body.
    fn obj_bytes(tag: u32) -> Vec<u8> {
        let mut v = tag.to_le_bytes().to_vec();
        v.resize(OBJECT_SIZE, 0);
        v
    }

    // Round-trip: build bytes for each variant, parse, check the fields read back.
    #[test]
    fn roundtrip_flat_binder_object() {
        let mut v = obj_bytes(BINDER_TYPE_BINDER);
        v[4..8].copy_from_slice(&0x1122_3344u32.to_le_bytes()); // flags
        v[8..16].copy_from_slice(&0xdead_beef_cafe_0001u64.to_le_bytes()); // binder/handle
        v[16..24].copy_from_slice(&0x9988_7766_5544_3322u64.to_le_bytes()); // cookie
        let mut r = SliceReader::new(&v);
        let o = BinderObjectBytes::read_from(&mut r).unwrap();
        assert_eq!(o.hdr_type(), BINDER_TYPE_BINDER);
        assert_eq!(o.fbo_flags(), 0x1122_3344);
        assert_eq!(o.fbo_binder(), 0xdead_beef_cafe_0001);
        assert_eq!(o.fbo_handle(), 0xcafe_0001); // low 32 bits of the union
        assert_eq!(o.fbo_cookie(), 0x9988_7766_5544_3322);
        assert_eq!(o.size(), 24);
    }

    #[test]
    fn roundtrip_fd_object() {
        let mut v = obj_bytes(BINDER_TYPE_FD);
        v[8..12].copy_from_slice(&7u32.to_le_bytes()); // fd
        v[16..24].copy_from_slice(&0x42u64.to_le_bytes()); // cookie
        let mut r = SliceReader::new(&v);
        let o = BinderObjectBytes::read_from(&mut r).unwrap();
        assert_eq!(o.hdr_type(), BINDER_TYPE_FD);
        assert_eq!(o.fdo_fd(), 7);
        assert_eq!(o.fdo_cookie(), 0x42);
        assert_eq!(o.size(), 24);
    }

    #[test]
    fn roundtrip_buffer_object() {
        let mut v = obj_bytes(BINDER_TYPE_PTR);
        v[8..16].copy_from_slice(&0x1000u64.to_le_bytes()); // buffer
        v[16..24].copy_from_slice(&0x200u64.to_le_bytes()); // length
        v[24..32].copy_from_slice(&3u64.to_le_bytes()); // parent
        v[32..40].copy_from_slice(&0x18u64.to_le_bytes()); // parent_offset
        let mut r = SliceReader::new(&v);
        let o = BinderObjectBytes::read_from(&mut r).unwrap();
        assert_eq!(o.hdr_type(), BINDER_TYPE_PTR);
        assert_eq!(o.bbo_buffer(), 0x1000);
        assert_eq!(o.bbo_length(), 0x200);
        assert_eq!(o.bbo_parent(), 3);
        assert_eq!(o.bbo_parent_offset(), 0x18);
        assert_eq!(o.size(), 40);
    }

    #[test]
    fn roundtrip_fd_array_object() {
        let mut v = obj_bytes(BINDER_TYPE_FDA);
        v[8..16].copy_from_slice(&5u64.to_le_bytes()); // num_fds
        v[16..24].copy_from_slice(&2u64.to_le_bytes()); // parent
        v[24..32].copy_from_slice(&0x10u64.to_le_bytes()); // parent_offset
        let mut r = SliceReader::new(&v);
        let o = BinderObjectBytes::read_from(&mut r).unwrap();
        assert_eq!(o.hdr_type(), BINDER_TYPE_FDA);
        assert_eq!(o.fdao_num_fds(), 5);
        assert_eq!(o.fdao_parent(), 2);
        assert_eq!(o.fdao_parent_offset(), 0x10);
        assert_eq!(o.size(), 32);
    }

    #[test]
    fn parse_one_accepts_valid_and_rejects_invalid() {
        assert_eq!(parse_one(&obj_bytes(BINDER_TYPE_BINDER)), Ok(24));
        assert_eq!(parse_one(&obj_bytes(BINDER_TYPE_PTR)), Ok(40));
        assert_eq!(parse_one(&obj_bytes(BINDER_TYPE_FDA)), Ok(32));
        // unknown tag -> EINVAL, no panic
        assert_eq!(parse_one(&obj_bytes(0xdead_beef)), Err(EINVAL));
        // valid tag but not enough bytes for that tag's size -> EINVAL
        let mut short = BINDER_TYPE_PTR.to_le_bytes().to_vec();
        short.resize(24, 0); // PTR needs 40
        assert_eq!(parse_one(&short), Err(EINVAL));
    }

    #[test]
    fn validators() {
        assert_eq!(ptr_align(1), Some(size_of::<usize>()));
        assert!(is_aligned(16, 8));
        assert_eq!(size_check(10, 5, 16), Ok(()));
        assert_eq!(size_check(usize::MAX, 1, 16), Err(EINVAL));
    }
}
