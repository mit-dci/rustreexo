// All ffi functions are defined as `unsafe` because they are meant to be called from
// C code, which is inherently unsafe. However, we check for null pointers and return
// EXIT_FAILURE if we encounter one. This is true for all functions in this crate,
// so it doesn't need to be repeated in every function as a `Safety` doc.
#![allow(clippy::missing_safety_doc)]
use bitcoin_hashes::{sha256, Hash};
use std::ops::Deref;

/// A raw hash passed from C, this is internally identical to [sha256::Hash] except that we use
/// use a repr(C) to make it compatible to how C stores data. Shouldn't be used anywhere else
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CHash([u8; 32]);

impl Deref for CHash {
    fn deref(&self) -> &Self::Target {
        &self.0
    }

    type Target = [u8; 32];
}
impl From<CHash> for sha256::Hash {
    fn from(val: CHash) -> Self {
        sha256::Hash::from_inner(*val)
    }
}

#[repr(C)]
pub enum Error {
    None = 0,
    NullPointer = 1,
    InvalidSlice = 2,
    UtreexoError = 3,
    AllocationError = 4,
    InvalidProof = 5,
}

pub const EXIT_SUCCESS: usize = 1;
pub const EXIT_FAILURE: usize = 0;
/// Checks if a pointer is null, if it is, returns EXIT_FAILURE.
/// If a pointer is null, and errno is not null, sets errno to
/// Error::NullPointer.
/// If a pointer is null, and count is greater than 0, sets errno
/// to Error::NullPointer.
/// The third case is used for slices, where we accept a NULL
/// pointer if the length is 0.
macro_rules! check_ptr {
    ($ptr: ident) => {
        if $ptr.is_null() {
            return crate::EXIT_FAILURE;
        }
    };
    ($errno: ident , $ptr: ident) => {
        if $ptr.is_null() {
            unsafe {
                *$errno = Error::NullPointer;
            }
            return crate::EXIT_FAILURE;
        }
    };
    ($errno: ident,$ptr: ident, $count: ident) => {
        if $ptr.is_null() && $count > 0 {
            unsafe {
                *$errno = Error::NullPointer;
            }
            return crate::EXIT_FAILURE;
        }
    };
}

/// Returns a static reference to the value pointed to by `thing`.
/// Because this is a reference, the value won't be dropped when the
/// function returns. If you need to free the value, use [get_owned].
fn get_safe_ty<T>(thing: *mut T) -> &'static T {
    unsafe { thing.as_ref().unwrap() }
}
/// Returns a mutable static reference to the value pointed to by `thing`.
fn get_safe_ty_mut<T>(thing: *mut T) -> &'static mut T {
    unsafe { thing.as_mut().unwrap() }
}
/// Returns an owned value pointed to by `thing`, if you don't need to
/// free the value, use [get_safe_ty].
fn get_owned<T>(thing: *mut T) -> Box<T> {
    unsafe { Box::from_raw(thing) }
}
/// Returns a slice of length `length` pointed to by `slice`. If `length` is 0,
/// returns an empty slice. We don't free the slice because it's a reference.
fn get_slice<'a, T>(slice: *mut T, length: usize) -> &'a [T] {
    if length == 0 {
        return &[];
    }
    unsafe { std::slice::from_raw_parts(slice, length) }
}
/// Returns a slice of length `length` pointed to by `slice`, where `slice` is
/// a [*const T] pointer. If `length` is 0, returns an empty slice.
fn get_slice_const<'a, T>(slice: *const T, length: usize) -> &'a [T] {
    if length == 0 {
        return &[];
    }
    unsafe { std::slice::from_raw_parts(slice, length) }
}

pub mod misc;
pub mod pollard;
pub mod proof;
pub mod stump;
