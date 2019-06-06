extern crate rustc_version;

use rustc_version::{Version, version};

fn main() {
    if version().unwrap() >= Version::parse("1.34.0").unwrap() {
        println!("cargo:rustc-cfg=nonzero_signed");
    }
}