#ifndef RUSTREEXO_STUMP
#define RUSTREEXO_STUMP
#include <inttypes.h>
#include <proof.h>

#ifdef __cplusplus
extern "C" {
#endif
/**
 * Stumps are a lightweight representation of the Utreexo state.
 * It has only the roots and the number of leaves. It can verify
 * all proofs, but can't prove. They are useful for clients and wallets.
 * For usage examples, see `examples/stump.c`
 */

/**
 * Modifies a Stump, adding new UTXOs and removing old ones, this function is
 * pure in relation to it's operands, meaning that it doesn't modify the Stump
 * passed in, but returns a new one in `out`.
 *
 * UTXOs and STXOs may be NULL, you just need to pass in the length of the
 * array as 0.
 *
 * Out:     errno:      The number representing an error while executing this
 *                      function.
 *          ret:        The new Stump
 *          stump:      The Stump being Updated
 *          udata:      The update data that can be used to update proofs. May be NULL.
 *
 * In:      utxos:          A array of hashes for the new UTXOs
 *          utxos_len:      The length of the array of hashes
 *          del_hashes:     A set with the hash for UTXOs being removed (STXOs)
 *          del_hashes_len: How many STXOs
 *          proof:          A proof for these STXOs, proving that they existed and
 *                          aren't being double-spent
 */
RUSTREEXO_MUST_USE size_t rustreexo_stump_modify(
    size_t *errno,
    rustreexo_stump *out,
    rustreexo_update_data *udata,
    rustreexo_stump stump,
    rustreexo_hash utxos[],
    size_t utxos_len,
    rustreexo_hash del_hashes[],
    size_t del_hashes_len,
    rustreexo_proof proof
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));

/**
 * Creates a new empty Stump. The caller is responsible for freeing the
 * returned Stump.
 *
 * Out:     errno:    The number representing an error while executing this function.
 *                    This function only fails if there is not enough memory to
 *                    allocate the Stump or `*stump` is NULL.
 * In:      stump:    A pointer to a Stump, it will be allocated by this function.
 */
RUSTREEXO_MUST_USE size_t rustreexo_stump_create(
    size_t *errno,
    rustreexo_stump *stump
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));

/**
 * Debug-prints a Stump. It should be a valid Stump created with the
 * `rustreexo_stump_create` method. If the provided Stump is invalid,
 * this function will be a no-op.
 *
 * In: stump: The Stump to be printed.
 */
RUSTREEXO_MUST_USE size_t rustreexo_stump_debug_print(
    rustreexo_stump stump
);

/**
 * Frees a Stump. It should be a valid Stump created with the
 * `rustreexo_stump_create`
 *
 * Out:     errno: The number representing an error while executing this function.
 * In:      stump: A valid Stump to be freed. It will be set to NULL after this
 *                 function is called.
 *
*/
RUSTREEXO_MUST_USE size_t rustreexo_stump_free(
    size_t *errno,
    rustreexo_stump stump
) RUSTREEXO_NON_NULL((1));

/**
 * Returns the roots of a Stump. It should be a valid Stump created with the
 * `rustreexo_stump_create` method. This function won't allocate any memory,
 * you should allocate in advance the array, that should be of size
 * `rustreexo_stump_get_num_roots * RUSTREEXO_HASH_SIZE`.
 *
 * Out:     errno:     The number representing an error while executing this function.
 *          ret:       A pointer to a rustreexo_hash array that will be filled with the
 *                     roots of the Stump.
 *          ret_len:   A pointer to a size_t that will be filled with the length of the
 *                     returned array.
 * In:      stump:     A valid Stump.
 */
RUSTREEXO_MUST_USE size_t rustreexo_stump_get_roots(
    size_t *errno,
    rustreexo_hash **ret,
    size_t *ret_len,
    rustreexo_stump stump
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2)) RUSTREEXO_NON_NULL((3));

/**
 * Frees a rustreexo_hash array returned by `rustreexo_stump_get_roots`.
 *
 * Out:    errno:   The number representing an error while executing this function
 *                  if any.
 * In:     roots:   A valid rustreexo_hash array.
 */
RUSTREEXO_MUST_USE size_t rustreexo_stump_roots_free(
    size_t *errno,
    rustreexo_hash *roots
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));

/**
 * Frees a rustreexo_update_data returned by `rustreexo_stump_modify`.
 * Out:     errno:    The number representing an error while executing this function
 * In:      udata:    The update data to be freed
 */
RUSTREEXO_MUST_USE size_t rustreexo_udata_free(
    size_t *errno,
    rustreexo_update_data udata
) RUSTREEXO_NON_NULL((1));


#ifdef __cplusplus
}
#endif
#endif // RUSTREEXO_STUMP