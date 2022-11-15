# BOOLE


## Tests

### Test Coverage
To get the test coverage, I use the [grcov](https://github.com/mozilla/grcov#how-to-get-grcov).
See the instructions [steps](https://github.com/mozilla/grcov#example-how-to-generate-source-based-coverage-for-a-rust-project).

```bash
export RUSTFLAGS="-Cinstrument-coverage"
export LLVM_PROFILE_FILE="./coverage/lib-%p-%m.profraw"
cargo build
cargo test
grcov ./coverage -s . --binary-path ./target/debug/ -t html --branch --ignore-not-existing -o ./target/debug/coverage/
open ./target/debug/coverage/index.html
```

### Property Based Testing
The library is using property based testing. It uses the [quickcheck](https://docs.rs/quickcheck/latest/quickcheck/) crate.

## Documentation

### Mathematical Expressions
Read more [here](https://docs.rs/rustdoc-katex-demo/0.1.5/rustdoc_katex_demo/) and [here](https://github.com/paulkernfeld/rustdoc-katex-demo).

```bash
set RUSTDOCFLAGS=--html-in-header katex-header.html
cargo doc --no-deps --open
```

## About

> Code designed and written on the beautiful island of [**Saaremaa**](https://goo.gl/maps/DmB9ewY2R3sPGFnTA), Estonia.