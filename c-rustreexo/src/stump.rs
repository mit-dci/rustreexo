use std::mem::ManuallyDrop;

use crate::{get_owned, get_safe_ty, get_slice, CHash, Error, EXIT_FAILURE, EXIT_SUCCESS};
use rustreexo::accumulator::{
    node_hash::NodeHash,
    proof::Proof,
    stump::{Stump, UpdateData},
};
#[no_mangle]
pub unsafe extern "C" fn rustreexo_stump_debug_print(stump: *mut Stump) -> usize {
    check_ptr!(stump);
    let stump = unsafe { stump.as_ref().unwrap() };
    println!("{:?}", stump);
    EXIT_SUCCESS
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_stump_modify(
    errno: *mut Error,
    ret: *mut *mut Stump,
    udata: *mut *mut UpdateData,
    stump: *mut Stump,
    utxos: *mut CHash,
    utxos_len: usize,
    del_hashes: *mut CHash,
    del_hashes_len: usize,
    proof: *mut Proof,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, stump);
    check_ptr!(errno, utxos, utxos_len);
    check_ptr!(errno, del_hashes, del_hashes_len);
    check_ptr!(errno, proof);
    check_ptr!(errno, ret);

    // Build a safe vector form a C array
    let utxos = get_slice(utxos, utxos_len);
    let utxos: Vec<_> = utxos.iter().map(|slice| NodeHash::from(**slice)).collect();

    let del_hashes = get_slice(del_hashes, del_hashes_len);
    let del_hashes = del_hashes
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();

    let proof = get_safe_ty(proof);
    let stump = get_owned(stump);
    let s = stump.modify(&utxos, &del_hashes, proof);
    if let Ok(s) = s {
        std::mem::drop(stump);
        unsafe {
            *ret = Box::into_raw(Box::new(s.0));
        }
        if !udata.is_null() {
            unsafe {
                *udata = Box::into_raw(Box::new(s.1));
            }
        }
        return EXIT_SUCCESS;
    }
    EXIT_FAILURE
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_stump_create(
    errno: *mut Error,
    stump: *mut *mut Stump,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, stump);
    unsafe {
        let s = Box::new(Stump::new());
        *stump = Box::into_raw(s);
    }
    EXIT_SUCCESS
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_stump_free(errno: *mut Error, stump: *mut Stump) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, stump);
    unsafe {
        let _ = Box::from_raw(stump);
    }
    EXIT_SUCCESS
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_stump_get_roots(
    errno: *mut Error,
    ret: *mut *mut CHash,
    ret_len: *mut usize,
    stump: *mut Stump,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, stump);
    check_ptr!(errno, ret);
    check_ptr!(errno, ret_len);
    let stump = get_safe_ty(stump);
    let roots = stump
        .roots
        .iter()
        .map(|hash| CHash(**hash))
        .collect::<Vec<_>>();
    unsafe {
        *ret_len = roots.len();
        // If we don't use ManuallyDrop here, the compiler will drop the vector.
        *ret = ManuallyDrop::new(roots.into_boxed_slice()).as_mut_ptr();
    }

    EXIT_SUCCESS
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_stump_roots_free(errno: *mut Error, roots: *mut CHash) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, roots);
    unsafe {
        let _ = Box::from_raw(roots);
    }
    EXIT_SUCCESS
}
// frees the udata
#[no_mangle]
pub unsafe extern "C" fn rustreexo_udata_free(errno: *mut Error, udata: *mut UpdateData) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, udata);
    unsafe {
        let _ = Box::from_raw(udata);
    }
    EXIT_SUCCESS
}
