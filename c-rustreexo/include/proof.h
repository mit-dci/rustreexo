#ifndef RUSTREEXO_PROOF_H
#define RUSTREEXO_PROOF_H
#include <stdlib.h>
#include <inttypes.h>
#include <stump.h>
#include <leaf.h>

/**
 * A proof is a collection of hashes and targets, used to prove that a set of
 * UTXOs actually belongs to a accumulator set. Those proofs are very similar
 * to Merkle proofs used in Bitcoin.
 */

#ifdef __cplusplus
extern "C"
{
#endif // __cplusplus
/**
* Creates a new rustreexo_proof from a set of hashes and targets. Hashes are
* the hash of each node needed to recompute a Merkle path leading to a root.
* Targets are the node number for UTXOs being spent.
* The caller is responsible for freeing the returned rustreexo_proof.
*
* Out:     errno:   A pointer used to write back error, if any
*          proof:   The newly created proof
* In:     hashes:   An array of hashes
*       n_hashes:   The hashes array's length
*        targets:   An array of targets
*      n_targets:   How many targets there are in targets
*/
RUSTREEXO_MUST_USE size_t rustreexo_proof_create(
    size_t *errno,
    rustreexo_proof *out,
    uint64_t *targets,
    size_t n_targets,
    rustreexo_hash *hashes,
    size_t n_hashes
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3)) RUSTREEXO_NON_NULL((5));

/**
 * Verifies if a rustreexo_proof is valid for a given Stump. It will return
 * error if the proof is invalid, with errno == ProofInvalid. Both
 * rustreexo_proof and Stump should be valid structures.
 *
 * Out:     errno:    A pointer used to write back error, if any
 * In:      stump:    The accumulator's state we should verify this rustreexo_proof
 *                    against
 *          proof:    An actual proof
 */
RUSTREEXO_MUST_USE size_t rustreexo_proof_verify(
    size_t *errno,
    rustreexo_hash *del_hashes,
    size_t n_dels,
    rustreexo_proof proof,
    rustreexo_stump stump
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));
/**
 * Deserializes a proof that was serialized with `rustreexo_proof_serialize`
 * Out:     errno:          A pointer used to write back error, if any
 * In:      parsed_proof:   The newly created proof object
 *          proof:          The serialized proof as a byte array
 *          length:         The length of the serialized proof
 */
RUSTREEXO_MUST_USE size_t rustreexo_proof_parse(
    size_t *errno,
    rustreexo_proof *parsed_proof,
    const char *proof,
    size_t length
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3));

/**
 * Serializes a proof. You should always serialize a proof before sending it
 * over the network, storing on disk or really doing anything that is not
 * call a rustreexo function. This is due the fact that `rustreexo_proof`
 * is a opaque structure, and you should not rely on its internal
 * representation.
 *
 * Out:     errno:      A pointer used to write back error, if any
 *          out:        A pointer to a char array that will be allocated
 *                      by this function
 * In:      ser_len:    The length of the serialized proof in bytes
 *          proof:      A proof to serialize, should be a valid `rustreexo_proof` element
 */
RUSTREEXO_MUST_USE size_t rustreexo_proof_serialize(
    size_t *errno,
    char **out,
    size_t *ser_len,
    rustreexo_proof proof
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3));

/**
 * Destroys a proof. This function should be called when you are done with
 * a proof and want to free its memory. The pointer will be set to NULL
 * after this function is called, so you should not use it anymore.
 *
 * Out:  errno:     A pointer used to write back error, if any
 * In:   proof:     A pointer to a proof to be freed, should be a valid
 *                  `rustreexo_proof` element.
 */
RUSTREEXO_MUST_USE size_t rustreexo_proof_free(
    size_t *errno,
    rustreexo_proof proof
) RUSTREEXO_NON_NULL((1));

/**
 * Debug print a proof, only useful during development, should not be used
 * in production. This function can't fail, if the proof is NULL, it will
 * just be a no-op.
 *
 * In:    proof:    A proof to be printed, should be a valid `rustreexo_proof`
 *                  element
 */
void rustreexo_proof_debug_print(
    rustreexo_proof proof
);
/**
 * Updates a proof after modifying a stump. This function will return a new
 * proof that is valid for the new stump. You can use it to keep your UTXO's
 * proofs up to date after a block is processed, so you always have valid
 * proofs if you need to spend your UTXOs.
 *
 *
 *Out: errno:               A pointer used to write back error, if any
 *     new_proof:           The newly created proof after update
 *     cached_hashes_out:   A list with the hashes that were cached in the stump
 *                          this might be exactly the same as cached_hashes, but
 *                          it might also be different if the stump was updated
 *                          and some hashes were removed from the stump.
 *     n_cached_hashes_out: The length of the cached_hashes array
 *In:  proof:               The proof to be updated, should be a valid `rustreexo_proof`
 *                          element and will be destroyed after this function is called.
 *     cached_hashes:       A list of hashes that were cached in the Stump before
 *                          the update. This list should be the same as the one used
 *                          to create the proof.
 *     n_cached_hashes:     The length of the cached_hashes array
 *     add_hashes:          A list of hashes that were added to the stump, that is, the
 *                          leaf hashes of the newly created UTXOs.
 *     n_add_hashes:        The length of the add_hashes array
 *     block_targets:       A list of targets that were removed from the stump,
 *     n_block_targets:     The length of the block_targets array
 *     remembers:           A list of the UTXOs we want to remember. The index is
 *                          the position in the n_add_hashes array, and this leaf
 *                          will be added as a target in the Proof. You should use
 *                          this to cache a proof for a UTXO
 *                          your wallet just received.
 *     n_remembers:         The length of the remembers array
 *     update_data:         Some internal data used to update the proof, this is
 *                          returned by `rustreexo_stump_modify` and should not be
 *                          modified manually.
 */
RUSTREEXO_MUST_USE size_t rustreexo_proof_update(
    size_t *errno,
    rustreexo_proof *new_proof,
    rustreexo_hash **cached_hashes_out,
    size_t *n_cached_hashes_out,
    rustreexo_proof proof,
    rustreexo_hash *cached_hashes,
    size_t n_cached_hashes,
    rustreexo_hash *add_hashes,
    size_t n_add_hashes,
    uint64_t *block_targets,
    size_t n_block_targets,
    uint64_t *remembers,
    size_t n_remembers,
    rustreexo_update_data update_data
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3));

/**
 * Frees a list of hashes. This function should be called when you are done
 * with the hashes from a proof
 *
 * Out:   errno:    A pointer used to write back error, if any
 * In:    hashes:   A list of hashes to be freed, should be a valid `rustreexo_hash`
 *                  vector.
*/
RUSTREEXO_MUST_USE size_t rustreexo_hashes_free(
    size_t *errno,
    rustreexo_hash *hashes
) RUSTREEXO_NON_NULL((1));

/**
 * Gets a subset of a proof. This function will return a new proof that
 * contains only the hashes that proves the new target list. This is
 * useful if you want to send a proof to a client, but you don't want
 * to send the whole proof, just the hashes that are relevant to the
 * client.
 *
 * Out:   errno:           A pointer used to write back error, if any
 *        new_proof:       The newly created proof after update
 *
 * In:    proof:           The proof to be updated, should be a valid `rustreexo_proof`
 *                         element and will be destroyed after this function is called.
 *        cached_hashes:   A list of hashes that were cached in the Stump before
 *                         the update. This list should be the same as the one used
 *                         to create the proof.
 *        nch:             The length of the cached_hashes array
 *        targets:         A list of targets that we want to prove. The index is
 *                         the position in the cached_hashes array, and this leaf
 *                         will be added as a target in the Proof. You should use
 *                         this to cache a proof for a UTXO your wallet just received.
 *        n_targets:       The length of the targets array
 *        n_leaves:        The number of leaves in the tree, this is used to calculate
*/
RUSTREEXO_MUST_USE size_t rustreexo_get_proof_subset(
    size_t *errno,
    rustreexo_proof *new_proof,
    rustreexo_proof proof,
    rustreexo_hash *cached_hashes,
    size_t n_cached_hashes,
    uint64_t *targets,
    size_t n_targets,
    size_t n_leaves
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));

#ifdef __cplusplus
}
#endif // __cplusplus

#endif // RUSTREEXO_PROOF_H