/*************************************************************************
 * Written in 2023 by Davidson Souza                                     *
 * To the extent possible under law, the author(s) have dedicated all    *
 * copyright and related and neighboring rights to the software in this  *
 * file to the public domain worldwide. This software is distributed     *
 * without any warranty. For the CC0 Public Domain Dedication, see       *
 * https://creativecommons.org/publicdomain/zero/1.0                     *
 *************************************************************************/
/*
    An extremely simple example of how to use the Stump API. This example
    creates a Stump, adds a leaf, creates a proof for that leaf, and then
    deletes the leaf using the proof.
    It should give you a nice grasp of how to use the API.
*/
#include <c-rustreexo.h>
#include <stdio.h>
#include <stdlib.h>

#define ARRAY_SIZE(x) sizeof(x) / sizeof((x)[0])

#define CHECK(x)                                                   \
    if (!x)                                                        \
    {                                                              \
        fprintf(stderr, "%s:%d: %s: %s\n", __FILE__, __LINE__, #x, \
                rustreexo_error_string(errno));                    \
        exit(1);                                                   \
    }

char spk = 0x51; // OP_TRUE, just a dummy script pubkey for this example

/* The leaf we will add and remove from the Accumulator */
static rustreexo_leaf_data leaves[] = {
    {
        .block_hash = {.inner = {
                           0x6f, 0x3e, 0xbc, 0x1f, 0x3f, 0xfd, 0xa3, 0xd3,
                           0x65, 0x15, 0xd6, 0x49, 0x79, 0x9b, 0x86, 0xff,
                           0x6f, 0xa8, 0x58, 0x89, 0x9a, 0x5c, 0xed, 0xff,
                           0x6e, 0x21, 0xbb, 0xa9, 0xe6, 0x95, 0x3f, 0x4b}},
        .prevout.tx_id = {.inner = {0x00, 0x3e, 0xbc, 0x1f, 0x3f, 0xfd, 0xa3, 0xd3, 0x65, 0x15, 0xd6, 0x49, 0x79, 0x9b, 0x86, 0xff, 0x6f, 0xa8, 0x58, 0x89, 0x9a, 0x5c, 0xed, 0xff, 0x6e, 0x21, 0xbb, 0xa9, 0xe6, 0x95, 0x3f, 0x4b}},
        .prevout.vout = 0,
        .utxo.script_pubkey = &spk,
        .utxo.script_pubkey_len = 1,
        .utxo.value = 51 // 0.00000051 BTC
    }};
/* The proof we will use to delete the leaf. It contains a collection of hashes
 * and the positions of what we are trying to prove */
static rustreexo_hash proofhashes[] = {{0}};
static unsigned int proof_pos[] = {0, 1, 2, 4};

int main()
{
    /* We'll use this in almost every function call to catch errors */
    size_t errno = -1;

    rustreexo_proof proof = {0};
    rustreexo_stump stump = {0};
    /* The has we'll add to the acc */
    rustreexo_hash leaf_hash = {0};
    /* Hashes a leaf */
    CHECK(rustreexo_leaf_hash(&errno, &leaf_hash, leaves[0]));
    /* The position of the leaf in the accumulator, since we'll only add one,
       we can know where it will be */
    size_t pos[] = {0};

    /* An empty proof */
    CHECK(rustreexo_proof_create(&errno, &proof, NULL, 0, NULL, 0));
    /* Create a new (empty) Stump, we need to do this to initialize `stump` */
    CHECK(rustreexo_stump_create(&errno, &stump));
    /* Add a leaf to our Stump */
    CHECK(rustreexo_stump_modify(&errno, &stump, NULL, stump, &leaf_hash, ARRAY_SIZE(leaves), NULL, 0, proof));
    /* Free this empty proof */
    CHECK(rustreexo_proof_free(&errno, proof));
    /* Create a valid proof for our leaf, in the current accumulator */
    CHECK(rustreexo_proof_create(&errno, &proof, pos, 1, NULL, 0));
    /* Delete our leaf, using the proof we just built */
    CHECK(rustreexo_stump_modify(&errno, &stump, NULL, stump, NULL, 0, &leaf_hash, ARRAY_SIZE(leaves), proof));
    /* Show the final Stump */
    CHECK(rustreexo_stump_debug_print(stump));

    /* Clean up */
    CHECK(rustreexo_stump_free(&errno, stump));
    /* Free the proof, we don't need it anymore */
    CHECK(rustreexo_proof_free(&errno, proof));
}
