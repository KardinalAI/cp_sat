extern crate prost_build;

fn main() {
    prost_build::compile_protos(
        &["src/cp_model.proto", "src/sat_parameters.proto"],
        &["src/"],
    )
    .unwrap();

    if std::env::var("DOCS_RS").is_err() {
        build_native();
    }
}

fn build_native() {
    let target_env = std::env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let is_msvc = target_env == "msvc";

    let ortools_prefix = std::env::var("ORTOOLS_PREFIX").unwrap_or_else(|_| {
        if cfg!(target_os = "windows") {
            r"C:\Program Files\ortools".into()
        } else {
            "/opt/ortools".into()
        }
    });
    println!("cargo:rerun-if-env-changed=ORTOOLS_PREFIX");

    let mut build = cc::Build::new();
    build
        .cpp(true)
        .file("src/cp_sat_wrapper.cpp")
        .include(format!("{}/include", ortools_prefix));

    if is_msvc {
        build
            .flag("/std:c++20")
            .flag("/EHsc")
            .define("OR_PROTO_DLL", Some("__declspec(dllimport)"));
    } else {
        build.flag("-std=c++20").define("OR_PROTO_DLL", Some(""));
    }

    build.compile("cp_sat_wrapper");

    println!("cargo:rustc-link-search=native={}/lib", ortools_prefix);
    println!("cargo:rustc-link-lib=dylib=ortools");

    // On Windows/MSVC, protobuf symbols are in a separate DLL
    if is_msvc {
        println!("cargo:rustc-link-lib=dylib=libprotobuf");
    }
}
