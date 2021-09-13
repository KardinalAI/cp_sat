//! The `cp_sat` crate provides an interface to [Google CP
//! SAT](https://developers.google.com/optimization/cp/cp_solver).
//!
//! # OR-Tools installation
//!
//! For `cp_sat` to work, you need to have a working OR-Tools
//! installation. By default, this crate will use the default C++
//! compiler, and add `/opt/ortools` in the search path. If you want
//! to provide your OR-Tools installation directory, you can define
//! the `ORTOOL_PREFIX` environment variable.
//!
//! # Brief overview
//!
//! The [builder::CpModelBuilder] provides an easy interface to
//! construct your problem. You can then solve and access to the
//! solver response easily. Here you can find the translation of the
//! first tutorial in the official documentation of CP SAT:
//!
//! ```
//! use cp_sat::builder::CpModelBuilder;
//! use cp_sat::proto::CpSolverStatus;
//!
//! fn main() {
//!     let mut model = CpModelBuilder::default();
//!
//!     let x = model.new_int_var_with_name([(0, 2)], "x");
//!     let y = model.new_int_var_with_name([(0, 2)], "y");
//!     let z = model.new_int_var_with_name([(0, 2)], "z");
//!
//!     model.add_ne(x, y);
//!
//!     let response = model.solve();
//!     println!(
//!         "{}",
//!         cp_sat::ffi::cp_solver_response_stats(&response, false)
//!     );
//!
//!     if response.status() == CpSolverStatus::Optimal {
//!         println!("x = {}", x.solution_value(&response));
//!         println!("y = {}", y.solution_value(&response));
//!         println!("z = {}", z.solution_value(&response));
//!     }
//! }
//! ```

#![deny(missing_docs)]

/// Model builder for ergonomic and efficient model creation.
pub mod builder;

/// Export of the CP SAT protobufs
#[allow(missing_docs, rustdoc::broken_intra_doc_links, rustdoc::bare_urls)]
pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/operations_research.sat.rs"));
}

/// Interface with the CP SAT functions.
pub mod ffi;
