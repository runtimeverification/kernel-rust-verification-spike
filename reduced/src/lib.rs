// SPDX-License-Identifier: GPL-2.0
//
// REDUCED, UNION-FREE extraction of spike_binder, for the Aeneas (LLBC -> Lean)
// step ONLY. See ../src/lib.rs for the full, faithful extraction and
// AENEAS-REPORT.md for why this reduced variant exists: Aeneas rejects `union`
// types outright, which aborts translation of the full crate before any Lean is
// emitted. This crate strips every union so the union-*free* logic can still be
// translated and reasoned about.
//
// Only the following items appear, matching the parent crate byte-for-byte
// except for the union removal noted below:
//   * type_to_size  (parent: BinderObject::type_to_size; here a free fn)
//   * ptr_align, is_aligned, size_check  (pure validators, verbatim)
//
// NOT present (cannot exist without unions): the BinderObject union, the
// BinderObjectRef view, and read_from / read_from_inner / as_ref / size /
// parse_one -- the type-punning deserializer core.

use core::mem::size_of;

// --- error handling: identical to parent crate -----------------------------
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error(pub i32);
pub const EINVAL: Error = Error(22);
pub type Result<T = ()> = core::result::Result<T, Error>;

// --- uapi struct layouts ---------------------------------------------------
// Same #[repr(C)] field order as the parent crate, EXCEPT each anonymous
// `union { u64; u32 }` is replaced by a plain `u64`. On a 64-bit target the
// union's size/alignment equal those of its largest member (u64, 8 bytes), so
// size_of::<T>() is byte-for-byte identical to the real (union-bearing) structs.
// type_to_size only ever observes these sizes, so it is preserved exactly.
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
        pub __bindgen_anon_1: u64, // was: union { binder: u64, handle: u32 }
        pub cookie: u64,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct binder_fd_object {
        pub hdr: binder_object_header,
        pub pad_flags: u32,
        pub __bindgen_anon_1: u64, // was: union { pad_binder: u64, fd: u32 }
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

// --- BINDER_TYPE_* constants: identical to parent crate ---------------------
pub const BINDER_TYPE_BINDER: u32 = 0x73622a85;
pub const BINDER_TYPE_WEAK_BINDER: u32 = 0x77622a85;
pub const BINDER_TYPE_HANDLE: u32 = 0x73682a85;
pub const BINDER_TYPE_WEAK_HANDLE: u32 = 0x77682a85;
pub const BINDER_TYPE_FD: u32 = 0x66642a85;
pub const BINDER_TYPE_FDA: u32 = 0x66646185;
pub const BINDER_TYPE_PTR: u32 = 0x70742a85;

// --- type_to_size: parent's BinderObject::type_to_size, verbatim body -------
// (Made a free `pub fn` since the `BinderObject` union that owned it cannot be
// expressed. The match arms and size_of expressions are unchanged.)
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

// --- pure validators: extracted byte-for-byte from the parent crate ---------
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

#[cfg(test)]
mod tests {
    use super::*;

    // The whole point of the union->u64 substitution: sizes must be unchanged.
    #[test]
    fn sizes_match_real_layout() {
        assert_eq!(size_of::<uapi::flat_binder_object>(), 24);
        assert_eq!(size_of::<uapi::binder_fd_object>(), 24);
        assert_eq!(size_of::<uapi::binder_buffer_object>(), 40);
        assert_eq!(size_of::<uapi::binder_fd_array_object>(), 32);
        assert_eq!(type_to_size(BINDER_TYPE_BINDER), Some(24));
        assert_eq!(type_to_size(BINDER_TYPE_PTR), Some(40));
        assert_eq!(type_to_size(BINDER_TYPE_FDA), Some(32));
        assert_eq!(type_to_size(0xdead_beef), None);
    }

    #[test]
    fn validators() {
        assert_eq!(ptr_align(1), Some(size_of::<usize>()));
        assert!(is_aligned(16, 8));
        assert_eq!(size_check(10, 5, 16), Ok(()));
        assert_eq!(size_check(usize::MAX, 1, 16), Err(EINVAL));
    }
}
