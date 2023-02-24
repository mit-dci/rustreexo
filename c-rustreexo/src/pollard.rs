use rustreexo::accumulator::{node_hash::NodeHash, pollard::Pollard, proof::Proof};

use crate::{
    get_safe_ty, get_safe_ty_mut, get_slice_const, CHash, Error, EXIT_FAILURE, EXIT_SUCCESS,
};

#[no_mangle]
unsafe extern "C" fn rustreexo_pollard_create(errno: *mut Error, ret: *mut *mut Pollard) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, ret);

    let pollard = Pollard::new();
    unsafe {
        ret.write(Box::into_raw(Box::new(pollard)));
    }
    EXIT_SUCCESS
}

#[no_mangle]
unsafe extern "C" fn rustreexo_pollard_modify(
    errno: *mut Error,
    pollard: *mut Pollard,
    utxos: *mut CHash,
    n_utxos: usize,
    stxos: *mut CHash,
    n_stxos: usize,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, pollard);
    check_ptr!(errno, utxos, n_utxos);
    check_ptr!(errno, stxos, n_stxos);

    let pollard = get_safe_ty_mut(pollard);
    let utxos = get_slice_const(utxos, n_utxos)
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();
    let stxos = get_slice_const(stxos, n_stxos)
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();

    match pollard.modify(&utxos, &stxos) {
        Ok(_) => EXIT_SUCCESS,
        Err(_) => {
            *errno = Error::UtreexoError;
            EXIT_FAILURE
        }
    }
}

#[no_mangle]
unsafe extern "C" fn rustreexo_pollard_prove(
    errno: *mut Error,
    out_proof: *mut *mut Proof,
    out_del_hashes: *mut *const CHash,
    n_del_hashes: *mut usize,
    pollard: *mut Pollard,
    targets: *mut CHash,
    n_targets: usize,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, pollard);
    check_ptr!(errno, targets, n_targets);
    check_ptr!(errno, out_proof);

    let pollard = get_safe_ty_mut(pollard);
    let targets = get_slice_const(targets, n_targets);
    let targets = targets
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();

    match pollard.prove(&targets) {
        Ok((proof, del_hashes)) => {
            let del_hashes = del_hashes
                .iter()
                .map(|&hash| CHash(*hash))
                .collect::<Vec<_>>();
            unsafe {
                out_proof.write(Box::into_raw(Box::new(proof)));
                out_del_hashes.write(del_hashes.as_ptr());
                n_del_hashes.write(del_hashes.len());
            }
            EXIT_SUCCESS
        }
        Err(_) => {
            *errno = Error::UtreexoError;
            EXIT_FAILURE
        }
    }
}

#[no_mangle]
unsafe extern "C" fn rustreexo_pollard_verify(
    errno: *mut Error,
    pollard: *mut Pollard,
    proof: *mut Proof,
    del_hashes: *mut CHash,
    n_del: usize,
) -> usize {
    check_ptr!(errno);
    check_ptr!(errno, pollard);
    check_ptr!(errno, proof);
    check_ptr!(errno, del_hashes, n_del);

    let pollard = get_safe_ty_mut(pollard);
    let proof = get_safe_ty(proof);
    let del_hashes = get_slice_const(del_hashes, n_del);
    let del_hashes = del_hashes
        .iter()
        .map(|hash| NodeHash::from(**hash))
        .collect::<Vec<_>>();

    match pollard.verify(&proof, &del_hashes) {
        Ok(valid) => {
            if valid {
                return EXIT_SUCCESS;
            }
            *errno = Error::UtreexoError;
            EXIT_FAILURE
        }
        Err(_) => {
            *errno = Error::UtreexoError;
            EXIT_FAILURE
        }
    }
}

#[no_mangle]
unsafe extern "C" fn rustreexo_pollard_free(pollard: *mut Pollard) -> usize {
    check_ptr!(pollard);

    let _ = Box::from_raw(pollard);
    EXIT_SUCCESS
}
