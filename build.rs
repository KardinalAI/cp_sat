extern crate prost_build;

use std::path::PathBuf;

const ORTOOLS_PREFIX_CANDIDATES: &[&str] = &[
    "/usr/local",
    "/usr",
    "/opt/homebrew",
    "/home/linuxbrew/.linuxbrew",
    "/opt/ortools",
];

// Find the OR-Tools installation prefix.
//
// Discovery order:
//   First: `$ORTOOLS_PREFIX` environment variable (prioritized override)
//   After:  sequentially checks candidates in `ORTOOLS_PREFIX_CANDIDATES` (see above)
//
// Returns `None` when no installation can be found.
fn find_ortools_prefix() -> Option<PathBuf> {
    if let Ok(prefix) = std::env::var("ORTOOLS_PREFIX") {
        let p = PathBuf::from(&prefix);
        // Honour the user's choice even if the header is missing
        return Some(p);
    }

    for candidate in ORTOOLS_PREFIX_CANDIDATES {
        let p = PathBuf::from(candidate);
        if p.join("include/ortools/sat/cp_model.h").exists() {
            return Some(p);
        }
    }

    None
}

// Error message listing every location that was probed.
fn build_error_message() -> String {
    let mut msg = String::from(
        "error: OR-Tools installation not found.\n\
         Tried the following locations:\n\n",
    );

    msg.push_str(" 1. $ORTOOLS_PREFIX (not set)\n");
    for (i, candidate) in ORTOOLS_PREFIX_CANDIDATES.iter().enumerate() {
        msg.push_str(&format!(" {}. {}\n", i + 2, candidate));
    }

    msg.push_str(
        "\nInstall OR-Tools (https://developers.google.com/optimization/install)\n\
         and either set ORTOOLS_PREFIX to the installation prefix or install\n\
         to one of the standard locations listed above.",
    );

    msg
}

fn main() {
    println!("cargo:rerun-if-env-changed=ORTOOLS_PREFIX");
    println!("cargo:rerun-if-changed=src/cp_sat_wrapper.cpp");
    println!("cargo:rerun-if-changed=src/cp_model.proto");
    println!("cargo:rerun-if-changed=src/sat_parameters.proto");

    if std::env::var("DOCS_RS").is_ok() {
        return;
    }

    prost_build::compile_protos(
        &["src/cp_model.proto", "src/sat_parameters.proto"],
        &["src/"],
    )
    .unwrap();

    // OR-Tools prefix discovery
    let prefix = match find_ortools_prefix() {
        Some(p) => p,
        None => {
            eprintln!("{}", build_error_message());
            std::process::exit(1);
        }
    };

    // C++ wrapper compilation
    cc::Build::new()
        .cpp(true)
        .flags(["-std=c++17", "-DOR_PROTO_DLL="])
        .file("src/cp_sat_wrapper.cpp")
        .include(prefix.join("include"))
        .compile("cp_sat_wrapper.a");

    // Linker configuration
    println!("cargo:rustc-link-lib=ortools");
    println!("cargo:rustc-link-lib=protobuf");

    let lib = prefix.join("lib");
    let lib64 = prefix.join("lib64");

    for dir in [&lib, &lib64] {
        if dir.exists() {
            println!("cargo:rustc-link-search=native={}", dir.display());
        }
    }

    // Linux RPATH injection
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    if target_os == "linux" {
        for dir in [&lib, &lib64] {
            if dir.exists() {
                println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir.display());
            }
        }
    }
}
