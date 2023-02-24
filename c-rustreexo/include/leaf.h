#ifndef RUSTREEXO_LEAF
#define RUSTREEXO_LEAF
#include <stdint.h>
#include <stddef.h>

/**
 * A C representation of a rustreexo_hash, which is a 32 byte array. The
 * internal byte-order is not specified, and should be treated as an opaque
 * type, only used inside the API.
 */
typedef struct rustreexo_hash
{
    unsigned char inner[32];
} rustreexo_hash;

/**
 * This struct represents a bitcoin outpoint, which is a reference to a
 * specific transaction output. It's defined as the id of the transaction
 * containing the output, and the index of this output.
 *
 * We commit to this data structure in the leaf hash, that's why it's
 * defined here.
 */
typedef struct rustreexo_bitcoin_outpoint
{
    rustreexo_hash tx_id;
    uint32_t vout;
} rustreexo_bitcoin_outpoint;

/**
 * This struct represents a bitcoin transaction output,
 * which is a value and a script pubkey.
 *
 * This also gets committed to in the leaf hash.
 */
typedef struct rustreexo_bitcoin_tx_out
{
    uint64_t value;
    size_t script_pubkey_len;
    char *script_pubkey;
} rustreexo_bitcoin_tx_out;

/**
 * The actual leaf data. This hash is the data we use to build the utreexo
 * tree. It contains the data needed to validate the utxo, and some useful
 * commitments, to harden against some weird collision attacks.
 */
typedef struct rustreexo_leaf_data
{
    // A commitment to the block creating this utxo
    rustreexo_hash block_hash;
    // The utxo's outpoint
    rustreexo_bitcoin_outpoint prevout;
    // Header code is a compact commitment to the block height and whether
    // or not this transaction is coinbase.
    uint32_t header_code;
    // The actual utxo
    rustreexo_bitcoin_tx_out utxo;

} rustreexo_leaf_data;

/**
 * Computes the hash of a given leaf, will only fail if provided pointers are
 * invalid.
 *
 * Out:    errno:       Error code
 *         hash:        Output hash
 * In:     leaf_data:   The actual leaf
 */
RUSTREEXO_MUST_USE size_t rustreexo_leaf_hash(
    size_t *errno,
    rustreexo_hash *hash,
    rustreexo_leaf_data leaf_data
) RUSTREEXO_NON_NULL((1)) RUSTREEXO_NON_NULL((2));

#endif // RUSTREEXO_LEAF