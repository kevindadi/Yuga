#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

#[macro_use]
extern crate log;

use std::env;

use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;

use rustc_middle::ty::TyCtxt;
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyDiagCtxt;
use yuga::log::Verbosity;
use yuga::report::{default_report_logger, init_report_logger, ReportLevel};
use yuga::{analyze, compile_time_sysroot, progress_info, YugaConfig, YUGA_DEFAULT_ARGS};

struct YugaCompilerCalls {
    config: YugaConfig,
}

impl YugaCompilerCalls {
    fn new(config: YugaConfig) -> YugaCompilerCalls {
        YugaCompilerCalls { config }
    }
}

impl rustc_driver::Callbacks for YugaCompilerCalls {
    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        yuga::log::setup_logging(self.config.verbosity).expect("Yuga failed to initialize");

        progress_info!("Yuga started");
        analyze(tcx, self.config.clone());
        progress_info!("Yuga finished");

        compiler.sess.dcx().abort_if_errors();
        Compilation::Stop
    }
}

/// Execute a compiler with the given CLI arguments and callbacks.
fn run_compiler(
    mut args: Vec<String>,
    callbacks: &mut (dyn rustc_driver::Callbacks + Send),
) -> i32 {
    // Make sure we use the right default sysroot. The default sysroot is wrong,
    // because `get_or_default_sysroot` in `librustc_session` bases that on `current_exe`.
    //
    // Make sure we always call `compile_time_sysroot` as that also does some sanity-checks
    // of the environment we were built in.
    // FIXME: Ideally we'd turn a bad build env into a compile-time error via CTFE or so.
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc_session would compute.
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }

    // Some options have different defaults in Yuga than in plain rustc; apply those by making
    // them the first arguments after the binary name (but later arguments can overwrite them).
    args.splice(
        1..1,
        yuga::YUGA_DEFAULT_ARGS.iter().map(ToString::to_string),
    );

    // Invoke compiler, and handle return code.
    let exit_code =
        rustc_driver::catch_fatal_errors(move || rustc_driver::run_compiler(&args, callbacks))
            .unwrap_or_else(|e| {
                error!("Fatal error: {:?}", e);
            });
    1
}

fn parse_config() -> (YugaConfig, Vec<String>) {
    // collect arguments
    let mut config = YugaConfig::default();

    let mut rustc_args = vec![];
    let mut args = std::env::args();

    while let Some(arg) = args.next() {
        let orig_arg = arg.clone();
        let (key, value) = match arg.contains('=') {
            true => {
                let str_vec: Vec<&str> = arg.split('=').collect();
                (String::from(str_vec[0]), Some(String::from(str_vec[1])))
            }
            false => (arg, None),
        };
        match &key[..] {
            "-v" => config.verbosity = Verbosity::Verbose,
            "-vv" => config.verbosity = Verbosity::Trace,
            "-Zsensitivity-high" => config.report_level = ReportLevel::Error,
            "-Zsensitivity-med" => config.report_level = ReportLevel::Warning,
            "-Zsensitivity-low" => config.report_level = ReportLevel::Info,
            "-Zgeneric-matches-all" => config.generic_matches_all = true,
            "-Zno-wildcard-field" => config.wildcard_field = false,
            "-Zno-pub-only" => config.pub_only = false,
            "-Zno-shallow-filter" => config.shallow_filter = false,
            "-Zno-alias-analysis" => config.alias_analysis = false,
            "-Zno-mir" => config.no_mir = true,
            "-Zfilter-by-drop-impl" => config.filter_by_drop_impl = true,
            // Take the name of the function to debug as an argument and assign it to config.debug_fn
            "-Zdebug-fn" => {
                config.debug_fn = Some(value.expect("Missing argument for -Zdebug-fn"));
            }
            "-Zreport-dir" => {
                config.report_dir = value.expect("Missing argument for -Zreport-dir");
            }
            _ => {
                rustc_args.push(orig_arg);
            }
        }
    }

    (config, rustc_args)
}
fn main() {
    rustc_driver::install_ice_hook("yuga", |_| {}); // ICE: Internal Compilation Error

    let exit_code = {
        // initialize the report logger
        // `logger_handle` must be nested because it flushes the logs when it goes out of the scope
        let (config, mut rustc_args) = parse_config();
        let _logger_handle = init_report_logger(default_report_logger());
        let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
        // init rustc logger
        if env::var_os("RUSTC_LOG").is_some() {
            rustc_driver::init_rustc_env_logger(&handler);
        }

        if let Some(sysroot) = compile_time_sysroot() {
            let sysroot_flag = "--sysroot";
            if !rustc_args.iter().any(|e| e == sysroot_flag) {
                // We need to overwrite the default that librustc would compute.
                rustc_args.push(sysroot_flag.to_owned());
                rustc_args.push(sysroot);
            }
        }

        // Finally, add the default flags all the way in the beginning, but after the binary name.
        rustc_args.splice(1..1, YUGA_DEFAULT_ARGS.iter().map(ToString::to_string));

        debug!("rustc arguments: {:?}", &rustc_args);
        run_compiler(rustc_args, &mut YugaCompilerCalls::new(config))
    };

    std::process::exit(exit_code)
}
