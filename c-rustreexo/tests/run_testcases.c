#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/evp.h>
#include <c-rustreexo.h>
typedef struct
{
    uint64_t *leaf_preimages;
    size_t preimage_count;
    uint64_t *target_values;
    char *proofhashes[64];
    char *expected_roots[64];
    size_t proofhashes_len;
    size_t expected_roots_len;
    size_t target_value_len;
} test_data_input;

typedef struct
{
    uint64_t *leaf_preimages;
    char *expected_roots[64];
    size_t expected_roots_len;
    size_t preimage_count;
} add_test_data_input;

#include "test_data.h"

/**
 * This struct is only used in these tests, and have nothing to do with Utreexo. It holds
 * the data needed to test the ffi methods, and is used to generate the test vectors.
 */
typedef struct
{
    uint64_t *leaf_preimages;
    size_t preimage_count;
    uint64_t *target_values;
    rustreexo_hash *proofhashes;
    rustreexo_hash *expected_roots;
    size_t proofhashes_len;
    size_t expected_roots_len;
    size_t target_value_len;
} test_data;

typedef struct
{
    uint64_t *leaf_preimages;
    char *expected_roots[32];
    size_t expected_roots_len;
    size_t preimage_count;
} add_test_data;

// Asserts that two CHashes are equal
#define assert_eq(left, right)                                                                                                \
    for (int _i = 0; _i < 32; _i++)                                                                                           \
    {                                                                                                                         \
        if (left[_i] != right[_i])                                                                                            \
        {                                                                                                                     \
            printf("\nAssertion failed, position %d: %02x != %02x\n", _i, (unsigned char)left[_i], (unsigned char)right[_i]); \
            exit(EXIT_FAILURE);                                                                                               \
        }                                                                                                                     \
    }

// Computes the sha256 of a uint8_t
static const void sha256(rustreexo_hash *out, uint8_t preimage)
{
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    const EVP_MD *md = EVP_sha256();
    unsigned int md_len;
    EVP_DigestInit_ex(mdctx, md, NULL);
    EVP_DigestUpdate(mdctx, &preimage, 1);
    EVP_DigestFinal_ex(mdctx, out->inner, &md_len);
    EVP_MD_CTX_free(mdctx);
}

// Runs some API method and checks if it returns an error. If it does, it prints the
// error and exits the program.
#define CHECK(exp)                                                                 \
    if (!exp)                                                                      \
    {                                                                              \
        char *error;                                                               \
        printf("%s:%d - %s\n", __FILE__, __LINE__, rustreexo_error_string(errno)); \
        exit(EXIT_FAILURE);                                                        \
    }

// Parses a hex string into a rustreexo_hash
static const void parse_hex(const char hex[64], char *out)
{
    for (size_t i = 0; i < 64; i += 2)
    {
        char buf[3] = {hex[i], hex[i + 1], 0};
        out[i / 2] = (uint8_t)strtol(buf, NULL, 16);
    }
}
// Parses an array of hex strings into an array of CHashes
static const void parse_hexes(char **hexes, size_t len, rustreexo_hash *out)
{

    for (size_t i = 0; i < len; i++)
    {
        parse_hex(hexes[i], out[i].inner);
    }
}
// Parses a test_data_input into a test_data, should be used before actually running the
// test case.
static const test_data parse_test_case(test_data_input data)
{
    rustreexo_hash proofhashes[data.proofhashes_len];
    rustreexo_hash expected_roots[data.expected_roots_len];

    parse_hexes(data.proofhashes, data.proofhashes_len, proofhashes);
    parse_hexes(data.expected_roots, data.expected_roots_len, expected_roots);

    test_data td = {
        .leaf_preimages = data.leaf_preimages,
        .target_values = data.target_values,
        .preimage_count = data.preimage_count,
        .proofhashes = malloc(sizeof(proofhashes)),
        .expected_roots = malloc(sizeof(expected_roots)),
        .proofhashes_len = data.proofhashes_len,
        .target_value_len = data.target_value_len};

    memcpy(td.expected_roots, expected_roots, sizeof(expected_roots));
    memcpy(td.proofhashes, proofhashes, sizeof(proofhashes));

    return td;
}

static const add_test_data parse_add_test_case(add_test_data_input data)
{
    char *expected_roots[32];
    for (size_t i = 0; i < data.expected_roots_len; i++)
    {
        expected_roots[i] = malloc(64);
        parse_hex(data.expected_roots[i], expected_roots[i]);
    }

    add_test_data td = {
        .leaf_preimages = data.leaf_preimages,
        .expected_roots = malloc(sizeof(expected_roots)),
        .expected_roots_len = data.expected_roots_len,
        .preimage_count = data.preimage_count};

    memcpy(td.expected_roots, expected_roots, sizeof(expected_roots));

    return td;
}
static const void run_add_test_case(add_test_data test)
{
    size_t errno = -1;
    rustreexo_proof proof;
    rustreexo_stump s;
    rustreexo_hash utxos[test.preimage_count];
    rustreexo_update_data update_data;
    rustreexo_hash *roots;
    size_t roots_len;

    for (unsigned int i = 0; i < test.preimage_count; ++i)
    {
        sha256(&utxos[i], test.leaf_preimages[i]);
    }

    CHECK(rustreexo_stump_create(&errno, &s));
    CHECK(rustreexo_proof_create(&errno, &proof, NULL, 0, NULL, 0));
    CHECK(rustreexo_stump_modify(&errno, &s, &update_data, s, utxos, test.preimage_count, NULL, 0, proof));

    CHECK(rustreexo_stump_get_roots(&errno, &roots, &roots_len, s));
    for (unsigned int i = 0; i < roots_len; ++i)
    {
        assert_eq(roots[i].inner, test.expected_roots[i]);
    }

    CHECK(rustreexo_proof_free(&errno, proof));
    CHECK(rustreexo_stump_free(&errno, s));
}
// Runs a test case
static const void run_test_case(test_data test)
{
    size_t errno = -1;
    rustreexo_proof proof;
    rustreexo_stump s;
    rustreexo_hash utxos[test.preimage_count];
    rustreexo_hash del_hashes[test.target_value_len];
    rustreexo_update_data update_data;

    for (unsigned int i = 0; i < test.preimage_count; ++i)
    {
        sha256(&utxos[i], test.leaf_preimages[i]);
    }
    for (unsigned int i = 0; i < test.target_value_len; ++i)
    {
        sha256(&del_hashes[i], test.target_values[i]);
    }

    // Create a new stump
    CHECK(rustreexo_stump_create(&errno, &s));
    // Create a new empty proof
    CHECK(rustreexo_proof_create(&errno, &proof, test.target_values, test.target_value_len, test.proofhashes, test.proofhashes_len));
    // Modify the stump
    CHECK(rustreexo_stump_modify(&errno, &s, &update_data, s, utxos, test.preimage_count, NULL, 0, proof));

    // Verify the proof
    CHECK(rustreexo_proof_verify(&errno, del_hashes, test.target_value_len, proof, s));

    // Get the roots for this rustreexo_stump
    rustreexo_hash *roots;
    size_t roots_len;
    CHECK(rustreexo_stump_get_roots(&errno, &roots, &roots_len, s));
    for (unsigned int i = 0; i < roots_len; ++i)
    {
        assert_eq(roots[i].inner, test.expected_roots[i].inner);
    }

    // cleanup
    CHECK(rustreexo_stump_free(&errno, s));
    CHECK(rustreexo_proof_free(&errno, proof));
    CHECK(rustreexo_stump_roots_free(&errno, roots));

    free(test.proofhashes);
    free(test.expected_roots);
}

int main()
{
    for (int i = 0; i < 4; ++i)
    {
        printf("Running test #%d... ", i);
        run_add_test_case(parse_add_test_case(insertion_tests[i]));
        printf("(OK)\n");
    }
    return EXIT_SUCCESS;
}
