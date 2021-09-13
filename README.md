# Google CP-SAT solver Rust bindings [![](https://img.shields.io/crates/v/cp_sat.svg)](https://crates.io/crates/cp_sat) [![](https://docs.rs/cp_sat/badge.svg)](https://docs.rs/cp_sat)

Rust bindings to the Google CP-SAT constraint programming solver.

To use this library, you need a C++ compiler and an installation of
google or-tools library files.

The environment variable `ORTOOLS_PREFIX` is used to find include
files and library files. If not setted, `/opt/ortools` will be added
to the search path (classical search path will also be used).
