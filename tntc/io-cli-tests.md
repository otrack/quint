This is a suite of blackbox integration tests for the `tntc` executable.
The tests in this file check that particular output is produced when
particular input is received.

These tests require [`txm`](https://www.npmjs.com/package/txm) to be installed:

```sh
npm install -g txm
```

All of the test inputs in the following test cases are commands executed by `bash`.

<!-- !test program
bash -
-->

### User error on parse with non-existent file

Regression test for [#215](https://github.com/informalsystems/tnt/issues/215).
We want to ensure we do not throw uncaught exceptions when the input file is
doesn't exist.

<!-- !test in non-existent file -->
    tntc parse ../examples/non-existent.file

<!-- !test exit 1 -->
<!-- !test err non-existent file -->
    error: file ../examples/non-existent.file does not exist


### User error on parse with invalid input

Running the parse command with an invalid input will return a non-zero exit code
and print the errors encountered.

NOTE: We use `sed` here to strip off the current working directory from the
error output, so that the test is consistent across different environments. The
redirects allow us to filter stderr instead of stdout.

<!-- !test in parsing invalid file -->
    tntc parse ./testFixture/_1011nameOutOfScope.tnt 2> >(sed "s:$(pwd):.:" >&2)


<!-- !test exit 1 -->
<!-- !test err parsing invalid file -->
```
./testFixture/_1011nameOutOfScope.tnt:5:11 - error: Couldn't resolve name x in definition for A, in module nameOutOfScope
5:   val A = x + 1
             ^

error: parsing failed in phase 2
```

### Module AST is written to `--out` with parse command

<!-- !test in module AST is output -->
```
tntc parse --out parse-out-example.json ../examples/tuples.tnt
cat parse-out-example.json | jq '.module.name'
rm parse-out-example.json
```

<!-- !test out module AST is output -->
```
"Tuples"
```

### Type and effect maps are output to `--out` with typecheck command

<!-- !test in type and effect maps are output -->
```
tntc typecheck --out typecheck-out-example.json ../examples/tuples.tnt > /dev/null
printf "first type: " && cat typecheck-out-example.json | jq '.types."4".type.kind'
printf "first effect: " && cat typecheck-out-example.json | jq '.effects."5".kind'
rm typecheck-out-example.json
```

<!-- !test out type and effect maps are output -->
```
first type: "tup"
first effect: "concrete"
```