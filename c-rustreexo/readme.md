Rustreexo native library bindings for C

This module contains native bindings to the Rustreexo lib, that can be called from C. The generated bindings are used to build bindings for other languages, such as Python. The bindings and header file are manually generated, to reduce overhead and improve API usability.

If your codebase is pure Rust, you should use the Rust lib itself, these bindings are only useful if you want to use Rustreexo in a C codebase. To use it in Rust, just add this to your `Cargo.toml`:

```toml
[dependencies]
rustreexo = "0.1.0"
```

## Building

To build the library, run `cargo build` in the root directory of this repository. The library will be built in `target/debug` or `target/release` depending on the build mode.

## Testing

To run the tests, run `cargo test` in the root directory of this repository. There are some C tests in `tests/c_tests.c` that can be build with `make tests`, they'll be available in `build/<test_name>`.

## Usage

To use the library, include the header file `c-rustreexo.c` in your C code. The library is built as a static library and a dynamic lib, so you'll need to link it to your program. The library is built with the name `librustreexo`, so you'll need to link it with `-l:librustreexo.so`. A basic example is available in `examples/simple_stump_example.c`, to build it, run `make examples`. If you didn't install the library, you'll need to run `export LD_LIBRARY_PATH=target/debug` before running the example.

## Installing

You may install this using `make install`, this will install the library in `/usr/lib` and the header file in `/usr/include`. You can override the install directory by setting the `PREFIX` variable, for example `make install PREFIX=/usr/`.

## License

This library is licensed under the MIT license. See the [LICENSE](../LICENSE) file for more details.

## Other language bindings

- [Python](https://pypi.org/project/pytreexo/)