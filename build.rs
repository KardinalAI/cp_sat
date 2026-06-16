extern crate prost_build;

fn main() {
    prost_build::compile_protos(
        &["src/cp_model.proto", "src/sat_parameters.proto"],
        &["src/"],
    )
    .unwrap();

    if std::env::var("DOCS_RS").is_err() {
        let ortools_prefix = std::env::var("ORTOOLS_PREFIX")
            .ok()
            .unwrap_or_else(|| "/opt/ortools".into());
        cc::Build::new()
            .cpp(true)
            // OR-Tools' published binaries are built with NDEBUG. Compiling the
            // wrapper against its headers without NDEBUG instantiates the
            // debug variant of Abseil's containers (e.g. the absl::flat_hash_map
            // behind sat::Model::GetOrCreate), which references debug-only Abseil
            // symbols absent from the release libs and is an ODR violation. Match
            // the library's configuration.
            .flags(["-std=c++17", "-DOR_PROTO_DLL=", "-DNDEBUG"])
            // Pull the OR-Tools headers in as system headers so their own
            // diagnostics (unused params, sign comparisons, ...) stay out of the
            // build log; warnings in our own wrapper still surface normally.
            .flag(&format!("-isystem{}/include", ortools_prefix))
            .file("src/cp_sat_wrapper.cpp")
            .compile("cp_sat_wrapper.a");

        println!("cargo:rustc-link-lib=dylib=ortools");
        println!("cargo:rustc-link-search=native={}/lib", ortools_prefix);
    }
}
