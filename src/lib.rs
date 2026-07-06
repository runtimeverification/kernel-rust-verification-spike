// SPDX-License-Identifier: GPL-2.0
//
// Derived from the Linux kernel, drivers/android/binder/allocation.rs (plus
// rust_binder_main.rs and thread.rs for the ptr_align/is_aligned/size_check
// helpers), tree version v7.2-rc2. Original authors: the Linux kernel
// contributors. The parsing logic is copied byte-for-byte; every deviation is
// marked `// SPIKE-STUB: <reason>`.

//! # spike-binder
//!
//! Standalone extraction of the Linux kernel Rust Binder driver's
//! **binder-object deserialization** logic, for a Charon (Aeneas toolchain)
//! extraction feasibility spike.
//!
//! ## Provenance
//!
//! Sources, all from Linux **v7.2-rc2**:
//!   - `drivers/android/binder/allocation.rs`      — the `BinderObject` deserializer
//!     (`read_from`, `read_from_inner`, `as_ref`, `size`, `type_to_size`) and the
//!     `BinderObjectRef` view enum.
//!   - `drivers/android/binder/thread.rs`          — `is_aligned`, and the offset
//!     validation used in `copy_transaction_data`.
//!   - `drivers/android/binder/rust_binder_main.rs`— `ptr_align`.
//!   - `include/uapi/linux/android/binder.h`       — the C `uapi` struct layouts
//!     and `BINDER_TYPE_*` constants.
//!
//! The parsing logic itself is kept **byte-for-byte identical** to the kernel
//! source. Every deviation is marked with `// SPIKE-STUB: <reason>`.

// SPIKE-STUB: the real driver is `#![no_std]` and pulls in the `kernel` crate.
// This crate is ordinary std Rust so it builds with stable cargo. No behavioural
// change to the parsing code — only the ambient environment differs.

use core::mem::{size_of, MaybeUninit};

// ---------------------------------------------------------------------------
// SPIKE-STUB: error handling.
//
// Kernel uses `kernel::error::{Result, Error}` where `Error` wraps a C errno and
// `Result<T> = core::result::Result<T, Error>`, and `EINVAL` is an `Error`
// constant. The deserializer only ever produces `EINVAL`, so we model the errno
// as a newtype and keep the exact `Result` / `EINVAL` spelling used in the source.
// ---------------------------------------------------------------------------
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error(pub i32);
pub const EINVAL: Error = Error(22);
pub const ENOMEM: Error = Error(12);
pub type Result<T = ()> = core::result::Result<T, Error>;

// ---------------------------------------------------------------------------
// SPIKE-STUB: transmute marker traits.
//
// In the kernel these live in `kernel::transmute` and are `unsafe` marker traits
// implemented (via bindgen/macros) for types whose every bit pattern is valid.
// The deserializer bounds `read`/`read_from` on `FromBytes`; we reproduce the
// markers verbatim. Only the definition site moves.
// ---------------------------------------------------------------------------
/// # Safety
/// Every initialized byte pattern must be a valid value of the type.
pub unsafe trait FromBytes {}
/// # Safety
/// The type must not have any padding/uninit bytes when viewed as bytes.
pub unsafe trait AsBytes {}

// ---------------------------------------------------------------------------
// SPIKE-STUB: `uapi` C struct layouts.
//
// In the kernel these are bindgen-generated from
// `include/uapi/linux/android/binder.h` and reached via `kernel::uapi`.
// Reproduced here with the same field order / `#[repr(C)]` layout so that
// `size_of` and union punning behave identically on a 64-bit target
// (binder_uintptr_t = binder_size_t = u64).
// ---------------------------------------------------------------------------
pub mod uapi {
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_object_header {
        pub type_: u32,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub union flat_binder_object__bindgen_ty_1 {
        pub binder: u64, // binder_uintptr_t
        pub handle: u32,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct flat_binder_object {
        pub hdr: binder_object_header,
        pub flags: u32,
        pub __bindgen_anon_1: flat_binder_object__bindgen_ty_1,
        pub cookie: u64, // binder_uintptr_t
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
        pub buffer: u64, // binder_uintptr_t
        pub length: u64, // binder_size_t
        pub parent: u64,
        pub parent_offset: u64,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_fd_array_object {
        pub hdr: binder_object_header,
        pub pad: u32,
        pub num_fds: u64, // binder_size_t
        pub parent: u64,
        pub parent_offset: u64,
    }
}

// SPIKE-STUB: `BINDER_TYPE_*` come from `kernel::uapi` (bindgen). The C source
// computes them with `B_PACK_CHARS(c1,c2,c3,c4)=(c1<<24)|(c2<<16)|(c3<<8)|c4` and
// `B_TYPE_LARGE = 0x85`. Values inlined here (verified against the C header).
pub const BINDER_TYPE_BINDER: u32 = 0x73622a85; // B_PACK_CHARS('s','b','*',0x85)
pub const BINDER_TYPE_WEAK_BINDER: u32 = 0x77622a85; // ('w','b','*',_)
pub const BINDER_TYPE_HANDLE: u32 = 0x73682a85; // ('s','h','*',_)
pub const BINDER_TYPE_WEAK_HANDLE: u32 = 0x77682a85; // ('w','h','*',_)
pub const BINDER_TYPE_FD: u32 = 0x66642a85; // ('f','d','*',_)
pub const BINDER_TYPE_FDA: u32 = 0x66646185; // ('f','d','a',_)
pub const BINDER_TYPE_PTR: u32 = 0x70742a85; // ('p','t','*',_)

// ---------------------------------------------------------------------------
// SPIKE-STUB: byte-source reader.
//
// Replaces `kernel::uaccess::UserSliceReader`, which copies from a *userspace*
// pointer with fallible `copy_from_user`. Here the same method surface
// (`len`, `clone_reader`, `read_slice`, `skip`) reads from an in-memory `&[u8]`.
// `read_from` (below) is kept byte-for-byte against this surface; only the
// reader type name changes.
// ---------------------------------------------------------------------------
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

    /// A reader over the same remaining bytes that does not advance `self`.
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
// Below: parsing logic extracted BYTE-FOR-BYTE from
// drivers/android/binder/allocation.rs (lines ~452-565), modulo:
//   * `pub(crate)` -> `pub`               (SPIKE-STUB: crate has no parent module)
//   * `UserSliceReader` -> `SliceReader`  (SPIKE-STUB: see reader stub above)
// The bodies of read_from/read_from_inner/as_ref/size/type_to_size are unchanged.
// ===========================================================================

/// A binder object as it is serialized.
///
/// # Invariants
///
/// All bytes must be initialized, and the value of `self.hdr.type_` must be one of the allowed
/// types.
#[repr(C)]
pub union BinderObject {
    hdr: uapi::binder_object_header,
    fbo: uapi::flat_binder_object,
    fdo: uapi::binder_fd_object,
    bbo: uapi::binder_buffer_object,
    fdao: uapi::binder_fd_array_object,
}

/// A view into a `BinderObject` that can be used in a match statement.
pub enum BinderObjectRef<'a> {
    Binder(&'a mut uapi::flat_binder_object),
    Handle(&'a mut uapi::flat_binder_object),
    Fd(&'a mut uapi::binder_fd_object),
    Ptr(&'a mut uapi::binder_buffer_object),
    Fda(&'a mut uapi::binder_fd_array_object),
}

impl BinderObject {
    pub fn read_from(reader: &mut SliceReader) -> Result<BinderObject> {
        let object = Self::read_from_inner(|slice| {
            let read_len = usize::min(slice.len(), reader.len());
            reader.clone_reader().read_slice(&mut slice[..read_len])?;
            Ok(())
        })?;

        // If we used a object type smaller than the largest object size, then we've read more
        // bytes than we needed to. However, we used `.clone_reader()` to avoid advancing the
        // original reader. Now, we call `skip` so that the caller's reader is advanced by the
        // right amount.
        //
        // The `skip` call fails if the reader doesn't have `size` bytes available. This could
        // happen if the type header corresponds to an object type that is larger than the rest of
        // the reader.
        //
        // Any extra bytes beyond the size of the object are inaccessible after this call, so
        // reading them again from the `reader` later does not result in TOCTOU bugs.
        reader.skip(object.size())?;

        Ok(object)
    }

    /// Use the provided reader closure to construct a `BinderObject`.
    ///
    /// The closure should write the bytes for the object into the provided slice.
    pub fn read_from_inner<R>(reader: R) -> Result<BinderObject>
    where
        R: FnOnce(&mut [u8; size_of::<BinderObject>()]) -> Result<()>,
    {
        let mut obj = MaybeUninit::<BinderObject>::zeroed();

        // SAFETY: The lengths of `BinderObject` and `[u8; size_of::<BinderObject>()]` are equal,
        // and the byte array has an alignment requirement of one, so the pointer cast is okay.
        // Additionally, `obj` was initialized to zeros, so the byte array will not be
        // uninitialized.
        (reader)(unsafe { &mut *obj.as_mut_ptr().cast() })?;

        // SAFETY: The entire object is initialized, so accessing this field is safe.
        let type_ = unsafe { obj.assume_init_ref().hdr.type_ };
        if Self::type_to_size(type_).is_none() {
            // The value of `obj.hdr_type_` was invalid.
            return Err(EINVAL);
        }

        // SAFETY: All bytes are initialized (since we zeroed them at the start) and we checked
        // that `self.hdr.type_` is one of the allowed types, so the type invariants are satisfied.
        unsafe { Ok(obj.assume_init()) }
    }

    pub fn as_ref(&mut self) -> BinderObjectRef<'_> {
        use BinderObjectRef::*;
        // SAFETY: The constructor ensures that all bytes of `self` are initialized, and all
        // variants of this union accept all initialized bit patterns.
        unsafe {
            match self.hdr.type_ {
                BINDER_TYPE_WEAK_BINDER | BINDER_TYPE_BINDER => Binder(&mut self.fbo),
                BINDER_TYPE_WEAK_HANDLE | BINDER_TYPE_HANDLE => Handle(&mut self.fbo),
                BINDER_TYPE_FD => Fd(&mut self.fdo),
                BINDER_TYPE_PTR => Ptr(&mut self.bbo),
                BINDER_TYPE_FDA => Fda(&mut self.fdao),
                // SAFETY: By the type invariant, the value of `self.hdr.type_` cannot have any
                // other value than the ones checked above.
                _ => core::hint::unreachable_unchecked(),
            }
        }
    }

    pub fn size(&self) -> usize {
        // SAFETY: The entire object is initialized, so accessing this field is safe.
        let type_ = unsafe { self.hdr.type_ };

        // SAFETY: The type invariants guarantee that the type field is correct.
        unsafe { Self::type_to_size(type_).unwrap_unchecked() }
    }

    fn type_to_size(type_: u32) -> Option<usize> {
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
}

// ===========================================================================
// Bonus: pure offset/length validators used on the userspace-transaction path.
// Extracted byte-for-byte:
//   * `ptr_align`  from rust_binder_main.rs:283
//   * `is_aligned` from thread.rs:39
//   * `size_check` logic from allocation.rs:82 (Allocation::size_check); turned
//     into a free function taking the buffer size explicitly.
// ===========================================================================

/// From `rust_binder_main.rs`. Rounds `value` up to a `usize` boundary, or
/// `None` on overflow.
pub fn ptr_align(value: usize) -> Option<usize> {
    let size = core::mem::size_of::<usize>() - 1;
    Some(value.checked_add(size)? & !size)
}

/// From `thread.rs`.
pub fn is_aligned(value: usize, to: usize) -> bool {
    value % to == 0
}

/// SPIKE-STUB: extracted from `Allocation::size_check` (allocation.rs:82). The
/// original is a method reading `self.size`; here `buffer_size` is passed
/// explicitly. Arithmetic (overflow + bounds check) is byte-for-byte identical.
pub fn size_check(offset: usize, size: usize, buffer_size: usize) -> Result {
    let overflow_fail = offset.checked_add(size).is_none();
    let cmp_size_fail = offset.wrapping_add(size) > buffer_size;
    if overflow_fail || cmp_size_fail {
        return Err(EINVAL);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// SPIKE-STUB: a small public driver so there is an easy top-level entry point
// for extraction/analysis. Not present in the kernel; exercises the extracted
// deserializer end-to-end over an in-memory byte buffer.
// ---------------------------------------------------------------------------
pub fn parse_one(bytes: &[u8]) -> Result<usize> {
    let mut reader = SliceReader::new(bytes);
    let obj = BinderObject::read_from(&mut reader)?;
    Ok(obj.size())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn flat_binder_object_bytes(type_: u32) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&type_.to_ne_bytes()); // hdr.type_
        v.extend_from_slice(&0u32.to_ne_bytes()); // flags
        v.extend_from_slice(&0u64.to_ne_bytes()); // union
        v.extend_from_slice(&0u64.to_ne_bytes()); // cookie
        // pad up to the largest object size so `read_from_inner` can fill it.
        while v.len() < size_of::<BinderObject>() {
            v.push(0);
        }
        v
    }

    #[test]
    fn parses_valid_binder_object() {
        let bytes = flat_binder_object_bytes(BINDER_TYPE_BINDER);
        assert_eq!(parse_one(&bytes), Ok(size_of::<uapi::flat_binder_object>()));
    }

    #[test]
    fn rejects_invalid_type() {
        let bytes = flat_binder_object_bytes(0xdead_beef);
        assert_eq!(parse_one(&bytes), Err(EINVAL));
    }

    #[test]
    fn validators() {
        assert_eq!(ptr_align(1), Some(size_of::<usize>()));
        assert!(is_aligned(16, 8));
        assert_eq!(size_check(10, 5, 16), Ok(()));
        assert_eq!(size_check(usize::MAX, 1, 16), Err(EINVAL));
    }
}
