#!/bin/python3
# -*- coding: utf-8 -*-

# This script parses the json of the rustreexo test suite and outputs a C header 
# file to be used in the C test suite.

import json
import sys

# This function parses a single entry of the json file and returns a string
# that can be used in a C header file.
def parse_entry_addition_test(entry, full: bool=False) -> str:
    result = "{\n"
    result += ".expected_roots=" + reduce_array_to_string(entry["expected_roots"]) + ",\n"
    result += ".leaf_preimages=(uint64_t[])" + reduce_array_to_string(entry["leaf_preimages"]) + ",\n"
    result += ".preimage_count=" + len(entry["leaf_preimages"]).__str__() + ",\n"
    result += ".expected_roots_len= " + len(entry["expected_roots"]).__str__() + ",\n"
    if full:
        result += "proofhashes_len: " + len(entry["proofhashes"]).__str__() + ",\n"
        result += "proofhashes: " + reduce_array_to_string(entry["proofhashes"]) + ",\n"
        result += "target_values: (uint64_t[])" + reduce_array_to_string(entry["target_values"]) + ",\n"
        result += "target_value_len: " + len(entry["target_values"]).__str__() + ",\n"
    result += "},"
    return result

# This function reduces a python array to a C array string.
def reduce_array_to_string(array):
    result = "{"
    for i in range(len(array)):
        if type(array[i]) == str:
            result += "\"" + array[i].__str__() + "\""
        else:
            result += array[i].__str__()
        if i != len(array) - 1:
            result += ", "
    result += "}"
    return result

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 parse_json.py <path_to_json_file>")
        return

    with open(sys.argv[1]) as f:
        data = json.load(f)
    data = data["insertion_tests"]
    final = "static const add_test_data_input insertion_tests[] = {\n"
    for i in range(len(data)):
        final += parse_entry_addition_test(data[i])
        final += "\n"
    final += "};"
    open("tests/test_data.h", "w").write(final)

main()