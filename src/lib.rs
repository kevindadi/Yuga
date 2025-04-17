#![feature(box_patterns)]
#![feature(rustc_private)]
#![feature(try_blocks)]
#![feature(never_type)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
// extern crate rustc_mir;
extern crate rustc_span;

extern crate bitflags;

#[macro_use]
extern crate if_chain;
#[macro_use]
extern crate log as log_crate;

#[macro_use]
mod macros;

mod analysis;
pub mod log;
pub mod paths;
pub mod report;
pub mod utils;

use rustc_middle::ty::TyCtxt;

use crate::analysis::LifetimeChecker;
use crate::log::Verbosity;
use crate::report::ReportLevel;

use std::time::Instant;

// Insert rustc arguments at the beginning of the argument list that Yuga wants to be
// set per default, for maximal validation power.
pub static YUGA_DEFAULT_ARGS: &[&str] = &["-Zalways-encode-mir", "-Zmir-opt-level=0", "--cfg=yuga"];

#[derive(Debug, Clone)]
pub struct YugaConfig {
    pub verbosity: Verbosity,
    pub report_level: ReportLevel,
    pub generic_matches_all: bool,
    pub wildcard_field: bool,
    pub pub_only: bool,
    pub shallow_filter: bool,
    pub alias_analysis: bool,
    pub no_mir: bool,
    pub filter_by_drop_impl: bool,
    pub debug_fn: Option<String>,
    pub report_dir: String,
}

impl Default for YugaConfig {
    fn default() -> Self {
        YugaConfig {
            verbosity: Verbosity::Normal,
            report_level: ReportLevel::Info,
            generic_matches_all: false,
            wildcard_field: true,
            pub_only: true,
            shallow_filter: true,
            alias_analysis: true,
            no_mir: false,
            filter_by_drop_impl: false,
            debug_fn: None,
            report_dir: String::from("yuga_reports"),
        }
    }
}

/// Returns the "default sysroot" that Yuga will use if no `--sysroot` flag is set.
/// Should be a compile-time constant.
pub fn compile_time_sysroot() -> Option<String> {
    // option_env! is replaced to a constant at compile time
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc.
        return None;
    }

    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default. The sysroot computation in librustc would
    // end up somewhere in the build dir.
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build Yuga without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

fn run_analysis<F, R>(name: &str, f: F) -> R
where
    F: FnOnce() -> R,
{
    let now = Instant::now();
    progress_info!("{} analysis started", name);
    let result = f();
    progress_info!("{} analysis finished", name);
    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);
    result
}

pub fn analyze<'tcx>(tcx: TyCtxt<'tcx>, config: YugaConfig) {
    // workaround to mimic arena lifetime
    let tcx = &*Box::leak(Box::new(tcx));

    run_analysis("LifetimeChecker", || {
        let checker = LifetimeChecker::new(tcx, config);
        checker.analyze();
    })
}
