#ifndef POLLARD_H
#define POLLARD_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <c-rustreexo.h>

/**
 * A full Pollard is a simple and efficient way to represent the forest on RAM. This technical
 * isn't a Pollard, because you can't prune leaves. But it's nice if you need a fast way to
 * prove arbitrary forest elements.
 *
 * This struct is a opaque type, so you can't access its fields directly. Use the functions
 * provided by this library to manipulate it. If you need the data, you can serialize it
 * with `rustreexo_pollard_serialize` and deserialize it with `rustreexo_pollard_deserialize`.
 */
typedef struct _pollard* rustreexo_pollard; // opaque type

/**
* Creates a new empty rustreexo_pollard. The caller is responsible for freeing the
* returned rustreexo_pollard. You can use this Pollard by updating it and
* proving/verifying proofs.
*
* Out:       errno:   A pointer used to write back error, if any
*          pollard:   The newly created Pollard
*/
RUSTREEXO_MUST_USE size_t rustreexo_pollard_create(
    size_t *errno,
    rustreexo_pollard *pollard
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));

/**
 * Updates a rustreexo_pollard with a set of hashes. You should use this function, instead
 * of directly calling add and del, because order matters.
 *
 * Out:        errno:   A pointer used to write back error, if any
 * In:       pollard:   The Pollard to update
 *        add_hashes:   An array of leaf hashes to add
 *      n_add_hashes:   The add_hashes array's length
 *        del_hashes:   An array of hashes to delete, that is, the inputs being spent
 *      n_del_hashes:   The del_hashes array's length
 */
RUSTREEXO_MUST_USE size_t rustreexo_pollard_modify(
    size_t *errno,
    rustreexo_pollard pollard,
    rustreexo_hash *add_hashes,
    size_t n_adds,
    rustreexo_hash *del_hashes,
    size_t n_dels
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3)) RUSTREEXO_NON_NULL((5));

/**
 * Proves a set of hashes against a rustreexo_pollard. The targets are the hashes you want to
 * prove. The proof is a rustreexo_proof type.
 *
 * Out:     errno:      A pointer used to write back error, if any
 *          proof:      The generated `rustreexo_proof` that can be serialized to send
 *                      to a verifier. The caller is responsible for freeing the returned
 *                      `rustreexo_proof`.
 *          hash:       Those are the hashes of the targets, but in the same order as the
 *                      proof.
 *          n_hashes:   The number of hashes in the proof, usually the same as the number
 *                      of targets.
 * In:      pollard:    The Pollard to prove against
 *          targets:    The hashes to prove, see leaf_hashes in leaf.h
 *          n_targets:  The number of targets
*/
RUSTREEXO_MUST_USE size_t rustreexo_pollard_prove(
    size_t *errno,
    rustreexo_proof *proof,
    rustreexo_hash **hash,
    size_t *n_hashes,
    rustreexo_pollard pollard,
    rustreexo_hash *targets,
    size_t n_targets
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3)) RUSTREEXO_NON_NULL((4)) RUSTREEXO_NON_NULL((6));

/**
 * Verifies a proof against a set of targets. The proof is a rustreexo_proof type.
 *
 * Out:     errno:    A pointer used to write back error, if any
 * in:      proof:    The proof to verify
 *           hash:    Those are the hashes of the targets, but in the same order as the
 *                    proof targets.
 *       n_hashes:    The number of targets in the proof.
 *        targets:    The hashes to prove, see leaf_hashes in leaf.h
 *      n_targets:    The number of targets
 */
RUSTREEXO_MUST_USE size_t rustreexo_pollard_verify(
    size_t *errno,
    rustreexo_proof proof,
    rustreexo_hash *hash,
    size_t n_hashes,
    size_t *targets,
    size_t n_targets
) RUSTREEXO_NON_NULL((1));

#ifdef __cplusplus
}
#endif

#endif // POLLARD_H