use std::{io::Cursor, mem::ManuallyDrop, vec};

use rustreexo::accumulator::{
    node_hash::NodeHash,
    proof::Proof,
    stump::{Stump, UpdateData},
};

use crate::{
    get_owned, get_safe_ty, get_slice, get_slice_const, CHash, Error, EXIT_FAILURE, EXIT_SUCCESS,
};

#[no_mangle]
pub unsafe extern "C" fn rustreexo_proof_create(
    errno: *mut Error,
    ret: *mut *mut Proof,
    targets: *mut u64,
    n_targets: usize,
    hashes: *mut CHash,
    n_hashes: usize,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, targets, n_targets);
    check_ptr!(errno, hashes, n_hashes);
    let targets = get_slice(targets, n_targets);
    let hashes = get_slice(hashes, n_hashes);
    let hashes = hashes
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();
    let proof = Proof::new(targets.to_vec(), hashes);
    unsafe {
        ret.write(Box::into_raw(Box::new(proof)));
    }

    EXIT_SUCCESS
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_proof_verify(
    errno: *mut Error,
    del_hashes: *mut CHash,
    n_del: usize,
    proof: *mut Proof,
    stump: *mut Stump,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, proof);
    check_ptr!(errno, stump);
    let proof = get_safe_ty(proof);
    let stump = get_safe_ty(stump);
    let hashes = get_slice_const(del_hashes, n_del);
    let hashes = hashes
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();
    match stump.verify(&proof, &hashes) {
        Ok(valid) => {
            if valid {
                return EXIT_SUCCESS;
            }
            unsafe {
                *errno = Error::InvalidProof;
            }
        }
        Err(_) => unsafe {
            *errno = Error::UtreexoError;
        },
    }
    EXIT_FAILURE
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_proof_parse(
    errno: *mut Error,
    parsed_proof: *mut *mut Proof,
    proof: *const u8,
    length: usize,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, parsed_proof);
    check_ptr!(errno, proof);
    let proof = get_slice_const(proof, length);
    let data = Cursor::new(proof);

    let proof = Proof::deserialize(data);
    if let Ok(proof) = proof {
        unsafe { parsed_proof.write(Box::into_raw(Box::new(proof))) };
        return EXIT_SUCCESS;
    }
    EXIT_FAILURE
}
#[no_mangle]
pub unsafe extern "C" fn rustreexo_proof_serialize(
    errno: *mut Error,
    out: *mut *mut u8,
    ser_len: *mut usize,
    proof: *mut Proof,
) -> usize {
    check_ptr!(errno);
    check_ptr!(out);
    check_ptr!(proof);

    let proof = get_safe_ty(proof);
    let mut serialized = vec![];
    if let Ok(len) = proof.serialize(&mut serialized) {
        unsafe {
            ser_len.write(len);
        }
        let mut proof = std::mem::ManuallyDrop::new(serialized);
        unsafe { out.write(proof.as_mut_ptr()) };
        return EXIT_SUCCESS;
    }
    EXIT_FAILURE
}
#[no_mangle]
pub unsafe extern "C" fn rustreexo_proof_free(errno: *mut Error, proof: *mut Proof) -> usize {
    check_ptr!(errno, proof);
    unsafe {
        let _ = Box::from_raw(proof);
    }
    EXIT_SUCCESS
}

#[no_mangle]
pub unsafe extern "C" fn rustreexo_proof_update(
    errno: *mut Error,
    new_proof: *mut *const Proof,
    cached_hashes_out: *mut *const CHash,
    n_cached_hashes_out: *mut usize,
    proof: *mut Proof,
    cached_hashes: *mut CHash,
    n_cached_hashes: usize,
    add_hashes: *mut CHash,
    n_add_hashes: usize,
    block_targets: *mut u64,
    n_block_targets: usize,
    remembers: *mut u64,
    n_remembers: usize,
    update_data: *mut UpdateData,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, proof);
    check_ptr!(errno, cached_hashes_out);
    check_ptr!(errno, new_proof);
    check_ptr!(errno, cached_hashes, n_cached_hashes);
    check_ptr!(errno, add_hashes, n_add_hashes);
    check_ptr!(errno, block_targets, n_block_targets);
    check_ptr!(errno, remembers, n_remembers);
    check_ptr!(errno, update_data);

    let proof = get_owned(proof);
    let cached_hashes = get_slice(cached_hashes, n_cached_hashes)
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();
    let add_hashes = get_slice(add_hashes, n_add_hashes)
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();
    let block_targets = get_slice(block_targets, n_block_targets);
    let remembers = get_slice(remembers, n_remembers);
    let update_data = get_safe_ty(update_data);

    match proof.update(
        cached_hashes.to_vec(),
        add_hashes.to_vec(),
        block_targets.to_vec(),
        remembers.to_vec(),
        update_data.to_owned(),
    ) {
        Ok((proof, cached_hashes)) => {
            unsafe {
                let cached_hashes = cached_hashes
                    .iter()
                    .map(|hash| CHash(**hash))
                    .collect::<Vec<_>>();
                new_proof.write(Box::into_raw(Box::new(proof)));
                n_cached_hashes_out.write(cached_hashes.len());
                let cached_hashes = ManuallyDrop::new(cached_hashes);
                cached_hashes_out.write(cached_hashes.as_ptr());
            }
            EXIT_SUCCESS
        }
        Err(_) => {
            unsafe {
                *errno = Error::UtreexoError;
            }
            EXIT_FAILURE
        }
    }
}
#[no_mangle]
pub unsafe extern "C" fn rustreexo_get_proof_subset(
    errno: *mut Error,
    new_proof: *mut *const Proof,
    proof: *mut Proof,
    node_hashes: *mut CHash,
    n_node_hashes: usize,
    targets: *mut u64,
    n_targets: usize,
    n_leaves: u64,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, proof);
    check_ptr!(errno, new_proof);
    check_ptr!(errno, targets, n_targets);
    check_ptr!(errno, node_hashes, n_node_hashes);

    let proof = get_safe_ty(proof);
    let targets = get_slice(targets, n_targets);
    let node_hashes = get_slice(node_hashes, n_node_hashes)
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();

    match proof.get_proof_subset(&node_hashes, &targets, n_leaves) {
        Ok(proof) => {
            unsafe {
                new_proof.write(Box::into_raw(Box::new(proof)));
            }
            EXIT_SUCCESS
        }
        Err(_) => {
            unsafe {
                *errno = Error::UtreexoError;
            }
            EXIT_FAILURE
        }
    }
}
#[no_mangle]
pub unsafe extern "C" fn rustreexo_hashes_free(errno: *mut Error, hashes: *mut CHash) -> usize {
    check_ptr!(errno, hashes);
    unsafe {
        let _ = Box::from_raw(hashes);
    }
    EXIT_SUCCESS
}
