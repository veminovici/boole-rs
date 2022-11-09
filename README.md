# BOOLE


## Tests

### Test Coverage
To get the test coverage, I use the [grcov](https://github.com/mozilla/grcov#how-to-get-grcov).
See the instructions [steps](https://github.com/mozilla/grcov#example-how-to-generate-source-based-coverage-for-a-rust-project).

```bash
export RUSTFLAGS="-Cinstrument-coverage"
export LLVM_PROFILE_FILE="./coverage/aabel-%p-%m.profraw"
cargo build
cargo test
grcov ./coverage -s . --binary-path ./target/debug/ -t html --branch --ignore-not-existing -o ./target/debug/coverage/
open ./target/debug/coverage/index.html
```

### Property Based Testing
The library is using property based testing. It uses the [quickcheck](https://docs.rs/quickcheck/latest/quickcheck/) crate.

## About

> Code designed and written on the beautiful island of [**Saaremaa**](https://goo.gl/maps/DmB9ewY2R3sPGFnTA), Estonia.