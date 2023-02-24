/*************************************************************************
 * Written in 2023 by Davidson Souza                                     *
 * To the extent possible under law, the author(s) have dedicated all    *
 * copyright and related and neighboring rights to the software in this  *
 * file to the public domain worldwide. This software is distributed     *
 * without any warranty. For the CC0 Public Domain Dedication, see       *
 * https://creativecommons.org/publicdomain/zero/1.0                     *
 *************************************************************************/

/**
 * A major part of the Utreexo accumulator is the proof. The proof is a list of
 * hashes that allows you to prove that a given element is in the accumulator.
 * A client'll use the proof to verify that a given element is in the accumulator,
 * and proceed to validate a transaction that spends that element.
 *
 * This example shows how to create a proof element, and how to verify it.
 */

#include <c-rustreexo.h>
#include <openssl/evp.h>
#include <stdio.h>
#include <stdlib.h>

#include "utils.h"

/* All hashes in a proof, this one is the first in `proof_tests`
   from `test_cases.json`
*/
struct rustreexo_hash proof_hashes[] = {
    {.inner = {0xdf, 0x46, 0xb1, 0x7b, 0xe5, 0xf6, 0x6f, 0x07, 0x50, 0xa4, 0xb3, 0xef, 0xa2, 0x6d, 0x46, 0x79, 0xdb, 0x17, 0x0a, 0x72, 0xd4, 0x1e, 0xb5, 0x6c, 0x3e, 0x4f, 0xf7, 0x5a, 0x58, 0xc6, 0x53, 0x86}},
    {.inner = {0x9e, 0xec, 0x58, 0x8c, 0x41, 0xd8, 0x7b, 0x16, 0xb0, 0xee, 0x22, 0x6c, 0xb3, 0x8d, 0xa3, 0x86, 0x4f, 0x95, 0x37, 0x63, 0x23, 0x21, 0xd8, 0xbe, 0x85, 0x5a, 0x73, 0xd5, 0x61, 0x6d, 0xcc, 0x73}}};

int main()
{
    size_t errno;
    rustreexo_proof proof, empty_proof;
    rustreexo_hash hashes[6];
    rustreexo_hash del_hashes[4];
    rustreexo_stump stump;
    rustreexo_update_data update_data;
    /* Targets are the position of the leafs being proven within the accumulator */
    size_t targets[] = {0, 1, 2, 3};
    /* The hashes of the leafs being added */
    for (int i = 0; i < ARRAY_SIZE(hashes); i++)
    {
        sha256(&hashes[i], i);
    }
    /* The hashes of the leafs being proved */
    for (int i = 0; i < ARRAY_SIZE(del_hashes); i++)
    {
        sha256(&del_hashes[i], targets[i]);
    }
    /* Creates an empty Stump */
    CHECK(rustreexo_stump_create(&errno, &stump));
    /* Create an empty proof we'll use to update the acc, since proof can't be
       null
    */
    CHECK(rustreexo_proof_create(&errno, &empty_proof, NULL, 0, NULL, 0));
    /* Add the hashes to the stump */
    CHECK(rustreexo_stump_modify(&errno, &stump, &update_data, stump, hashes, ARRAY_SIZE(hashes), NULL, 0, empty_proof));
    /* Create a proof for 0, 1, 2 and three, with `proof_hashes` */
    CHECK(rustreexo_proof_create(&errno, &proof, targets, ARRAY_SIZE(targets), hashes, ARRAY_SIZE(hashes)));
    /* Verify the proof */
    CHECK(rustreexo_proof_verify(&errno, del_hashes, ARRAY_SIZE(del_hashes), proof, stump))

    /* All objects in c-rustreexo are allocated on-demand using the *-create
       functions. As always with explicit allocation, you need to explicitly
       deallocate them, by calling the *-free methods.
    */
    CHECK(rustreexo_proof_free(&errno, proof));
    CHECK(rustreexo_stump_free(&errno, stump));
}