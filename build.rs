use std::error;

fn main() -> Result<(), Box<dyn error::Error>> {
    println!("cargo:rerun-if-changed=src/fun.lalrpop");

    lalrpop::process_root()
}
