#/bin/bash -e
# Runs all examples and tests in valgrind to check for memory leaks, read-after-free, read
# from uninitialized memory, etc.

export LD_LIBRARY_PATH=../target/debug

make build-debug && make examples

run_in_vg() {
    # Run the test in valgrind
    valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes --verbose --log-file=valgrind-out.txt $1 &> /dev/null
    # if there's no error summary, then there's no errors
    if ! grep -q "ERROR SUMMARY: 0 errors" valgrind-out.txt; then
        echo "Valgrind found errors in $1"
        mv valgrind-out.txt crash-$(date +%s)-$2.txt
        exit 1
    fi
    echo "(passed)"
    rm valgrind-out.txt
}

# run examples
ls ./examples/ | while read line; do
    # run the case if it doesn't end in .c or .h
    if [[ $line != *.c ]] && [[ $line != *.h ]]; then
        echo -n "Running $line..."
        run_in_vg "./examples/$line" $line
    fi
done

# run tests
ls ./tests/ | while read line; do
    # run the case if it doesn't end in .c or .h
    if [[ $line != *.c ]] && [[ $line != *.h ]]; then
        echo -n "Running $line..."
        run_in_vg "./tests/$line" $line
    fi
done
