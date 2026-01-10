#!/bin/bash

SCANNER="target/debug/rust-compiler"
PUBLIC_ROOT="tests/phase1-scanner/public"
PRIVATE_ROOT="tests/private-tests-main/scanner"
TIMEOUT=5
COUNT=0
TOTAL=0

cargo build

run_tests () {
    COUNT=0
    TOTAL=0
    for filename in "$1"/input/*.dcf; do
        touch tests/tmp.out
        echo "Testing: $filename"
        outname="$(basename "${filename%.dcf}.out")"
        timeout $TIMEOUT $SCANNER --target scan $filename --output tmp.out
        if [[ $filename == *invalid* ]]; then
            if grep -q "Error" tmp.out; then
                echo "Pass (invalid): $(basename "$filename")"
                COUNT=$((COUNT+1))
            else
                echo "Fail (invalid): $(basename "$filename")"
            fi
        else
            if diff tmp.out $1/output/$outname; then
                echo "Pass: $(basename $filename)"
                COUNT=$((COUNT+1))
            else
                echo "Fail: $(basename $filename)"
            fi
        fi
        TOTAL=$((TOTAL+1))
        rm -f tests/tmp.out
    done
    echo "Passed $COUNT out of $TOTAL scanner tests"
}

if [[ $1 == "public" ]]; then
    echo "Running public tests"
    run_tests $PUBLIC_ROOT
else
    echo "Running public tests"
    run_tests $PUBLIC_ROOT
    # echo "Running private tests"
    # run_tests $PRIVATE_ROOT 
fi
