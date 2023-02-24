#include <c-rustreexo.h>
#include <openssl/evp.h>
#include <stdio.h>
#include <stdlib.h>
/* The length of a static array */
#define ARRAY_SIZE(x) sizeof(x) / sizeof((x)[0])
/* A simple wrapper that checks if the command runs correctly, and prints
 * the error if it doesn't
 */
#define CHECK(x)                                                   \
    if (!x)                                                        \
    {                                                              \
        fprintf(stderr, "%s:%d: %s: %s\n", __FILE__, __LINE__, #x, \
                rustreexo_error_string(errno));                    \
        exit(1);                                                   \
    }
/* Computes the sha256 of a uint8_t */
static void sha256(rustreexo_hash *out, uint8_t preimage)
{
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    const EVP_MD *md = EVP_sha256();
    unsigned int md_len;
    EVP_DigestInit_ex(mdctx, md, NULL);
    EVP_DigestUpdate(mdctx, &preimage, 1);
    EVP_DigestFinal_ex(mdctx, out->inner, &md_len);
    EVP_MD_CTX_free(mdctx);
}