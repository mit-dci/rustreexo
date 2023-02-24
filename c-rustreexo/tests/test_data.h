static const add_test_data_input insertion_tests[] = {
    {
        .expected_roots = {"b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42"},
        .leaf_preimages = (uint64_t[]){0, 1, 2, 3, 4, 5, 6, 7},
        .preimage_count = 8,
        .expected_roots_len = 1,
    },
    {
        .expected_roots = {"df46b17be5f66f0750a4b3efa26d4679db170a72d41eb56c3e4ff75a58c65386", "9eec588c41d87b16b0ee226cb38da3864f9537632321d8be855a73d5616dcc73", "67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6"},
        .leaf_preimages = (uint64_t[]){0, 1, 2, 3, 4, 5, 6},
        .preimage_count = 7,
        .expected_roots_len = 3,
    },
    {
        .expected_roots = {"b151a956139bb821d4effa34ea95c17560e0135d1e4661fc23cedc3af49dac42", "9c053db406c1a077112189469a3aca0573d3481bef09fa3d2eda3304d7d44be8", "55d0a0ef8f5c25a9da266b36c0c5f4b31008ece82df2512c8966bddcc27a66a0", "4d7b3ef7300acf70c892d8327db8272f54434adbc61a4e130a563cb59a0d0f47"},
        .leaf_preimages = (uint64_t[]){0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14},
        .preimage_count = 15,
        .expected_roots_len = 4,
    },
    {
        .expected_roots = {"950c36521c4a3fa45862f31682f68b26af1e4a486fbf4d7f779a4bfcb8c9bbe9", "c9e5725dcf415c6eb0a2d381aa8b7678bc7a810ec46d8f330d4ef3ce023858bf", "a2402edac76acbf77c01dce0cdf0fbcf5e6e1acdf9eb97b891c2a6dc8582086a", "bb2202e245081accf9dfebba226acdef30ba221c8350ef5c707b0f9d294afe08", "252f10c83610ebca1a059c0bae8255eba2f95be4d1d7bcfa89d7248a82d9f111"},
        .leaf_preimages = (uint64_t[]){70, 13, 55, 152, 74, 33, 39, 122, 252, 53, 224, 211, 11, 25, 122, 14, 191, 152, 115, 205, 160, 163, 90, 191, 199, 242, 216, 32, 141, 6, 200, 109, 211, 53, 72, 250, 108, 163, 224, 90, 17, 25, 92, 254, 172, 211, 26, 231, 254, 159, 183, 180, 135, 131, 194, 83, 207, 158, 226, 49, 138, 136, 73, 143, 105, 164, 50, 58, 94, 168, 90, 128, 132, 238, 168, 47, 153, 20, 90, 106, 113, 168, 27, 136, 206, 3, 117, 87, 213, 48, 104, 7, 59, 167, 164, 161, 151, 11, 63, 145, 61, 24, 40, 231, 49, 78, 86, 52, 208, 35, 97, 15, 215, 238, 255, 227, 180, 226, 18, 223, 126, 157, 123, 81, 149, 46, 133, 132, 173, 190, 87, 227, 139, 199, 209, 17, 210, 112, 204, 177, 71, 195, 56, 23, 67, 15, 226, 97, 62, 7, 235, 63, 200, 140, 104, 4, 130, 47, 168, 33, 122, 118, 169, 129, 20, 186, 121, 114, 107, 79, 215, 226, 45, 0, 108, 43, 53, 218, 252, 71, 176, 54, 93, 0, 168, 238, 209, 41, 198, 111, 235, 215, 216, 60, 135, 230, 205, 177, 102},
        .preimage_count = 199,
        .expected_roots_len = 5,
    },
};