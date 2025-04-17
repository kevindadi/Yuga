#![allow(unused_parens)]

mod alias;
mod checks;
pub mod iterators;
mod mirfunc;
pub mod process;
mod report;
mod taint;
pub mod utils;

use rustc_hash::FxHashMap;
use utils::{get_actual_type, get_first_field, get_mir_value_from_hir_param, get_name_from_param};

use report::{
    arg_arg_uaf_report, arg_return_mut_report, arg_return_uaf_report, generate_llm_query,
};

use process::{get_implicit_lifetime_bounds, get_sub_types, get_sub_types_dbg};

use alias::AliasAnalyzer;
use iterators::fn_iter;
use mirfunc::MirFunc;
use taint::TaintAnalyzer;

use crate::YugaConfig;
use crate::{progress_info, progress_warn};

use rustc_middle::mir::{Local, Place};
use rustc_middle::ty::TyCtxt;

use std::collections::HashMap;
use std::fs;

// use rand::{distributions::Alphanumeric, Rng}; // 0.8

pub struct Report {
    html: String,
    markdown: String,
    func_name: String,
    error_type: String,
    queries: Vec<String>,
}

pub struct LifetimeChecker<'tcx> {
    tcx: &'tcx TyCtxt<'tcx>,
    config: YugaConfig,
}

impl<'tcx> LifetimeChecker<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt<'tcx>, config: YugaConfig) -> Self {
        LifetimeChecker { tcx, config }
    }

    fn debug_output<'a>(&self, func: &MirFunc<'tcx, 'a>) {
        for (inp_num1, inp1) in func.fn_sig.decl.inputs.iter().enumerate() {
            let subtypes = get_sub_types_dbg(
                inp1,
                &func.generic_bounds,
                self.tcx,
                Vec::new(),
                FxHashMap::default(),
                FxHashMap::default(),
                false,
            );

            println!("Arg {} Data lifetimes: {:#?}", inp_num1, subtypes);

            let bounds = get_implicit_lifetime_bounds(inp1, &func.generic_bounds, self.tcx);

            println!("Arg {} Implicit bounds: {:#?}", inp_num1, bounds);
        }

        if let rustc_hir::FnRetTy::Return(ret_type) = func.fn_sig.decl.output {
            let subtypes = get_sub_types_dbg(
                ret_type,
                &func.generic_bounds,
                self.tcx,
                Vec::new(),
                FxHashMap::default(),
                FxHashMap::default(),
                false,
            );

            let bounds = get_implicit_lifetime_bounds(ret_type, &func.generic_bounds, self.tcx);
            println!("Return type data lifetimes: {:#?}", subtypes);
            println!("Return type implicit bounds: {:#?}", bounds);
        }
    }

    fn check_arg_return_violations<'a>(&self, func: &MirFunc<'tcx, 'a>) -> Option<Report> {
        let mut taint_analyzer = TaintAnalyzer::new(&func.mir_body, self.config.clone());
        let mut alias_analyzer = AliasAnalyzer::new(&func.mir_body, self.config.clone());

        if let rustc_hir::FnRetTy::Return(ret_type) = func.fn_sig.decl.output {
            let ret_subtypes = get_sub_types(ret_type, &func.generic_bounds, self.tcx);
            // We shouldn't get implicit bounds from the return type, because
            // that is what we're *creating*. We can only assume bounds based on what is *given to us*,
            // namely the arguments.

            for (inp_num, inp) in func.fn_sig.decl.inputs.iter().enumerate() {
                let inp_subtypes = get_sub_types(inp, &func.generic_bounds, self.tcx);
                let mut bounds = get_implicit_lifetime_bounds(inp, &func.generic_bounds, self.tcx);

                bounds.append(&mut func.lifetime_bounds.clone());

                for tgt_ty in ret_subtypes.iter() {
                    for src_ty in inp_subtypes.iter() {
                        if self.config.generic_matches_all {
                            // def_id `None` matches everything
                            if src_ty.def_id.is_some()
                                && tgt_ty.def_id.is_some()
                                && (src_ty.def_id != tgt_ty.def_id)
                                && (!src_ty.is_closure)
                                && (!tgt_ty.is_closure)
                            {
                                continue;
                            }
                        } else {
                            // def_id `None` only matches `None`
                            if src_ty.def_id != tgt_ty.def_id
                                && (!src_ty.is_closure)
                                && (!tgt_ty.is_closure)
                            {
                                continue;
                            }
                        }

                        let source_field = get_first_field(&src_ty.projection);
                        let target_field = get_first_field(&tgt_ty.projection);

                        let mut debug = false;
                        if let Some(ref debug_fn) = self.config.debug_fn {
                            if func.func_name.contains(debug_fn) {
                                debug = true;
                            }
                        }
                        // First check for use-after-free violations
                        let (
                            violation,
                            (src_bounding_lt, tgt_bounding_lt),
                            (src_is_raw, tgt_is_raw),
                        ) = checks::arg_return_outlives(
                            &src_ty,
                            &tgt_ty,
                            &bounds,
                            &self.tcx,
                            self.config.clone(),
                            debug,
                        );

                        if violation {
                            let source_place: Option<Place> =
                                get_mir_value_from_hir_param(&func.params[inp_num], &func.mir_body);
                            if source_place.is_none() {
                                continue;
                            }
                            let source_place = source_place.unwrap();
                            let mut debug = false;
                            let dataflow_detected: bool;

                            if self.config.no_mir {
                                dataflow_detected = true;
                            } else if self.config.alias_analysis {
                                dataflow_detected = alias_analyzer.check_alias(
                                    &source_place.local,
                                    &src_ty.projection,
                                    &Local::from_usize(0),
                                    &tgt_ty.projection,
                                    debug,
                                );
                                alias_analyzer.reset();
                            } else {
                                taint_analyzer.mark_taint(&source_place.local, source_field, debug);
                                dataflow_detected =
                                    taint_analyzer.check_taint(&Local::from_usize(0), target_field);
                            }
                            if dataflow_detected {
                                let (html, markdown) = arg_return_uaf_report(
                                    self.tcx,
                                    &func,
                                    inp_num,
                                    src_ty,
                                    tgt_ty,
                                    src_bounding_lt,
                                    tgt_bounding_lt,
                                );
                                let mut queries: Vec<String> = Vec::new();
                                if src_ty.in_struct {
                                    let arg_name =
                                        get_name_from_param(&func.params[inp_num]).unwrap();
                                    queries.push(generate_llm_query(
                                        self.tcx,
                                        arg_name.to_string(),
                                        get_actual_type(inp, self.tcx).span,
                                        src_ty,
                                    ));
                                }
                                // if tgt_ty.in_struct && tgt_is_raw {
                                //     queries.push(generate_llm_query(self.tcx, "ret".to_string(), ret_type.span, tgt_ty));
                                // }
                                return Some(Report {
                                    html,
                                    markdown,
                                    func_name: String::new(),
                                    error_type: "uaf".to_string(),
                                    queries,
                                });
                            }
                            taint_analyzer.clear_taint();
                        }

                        let mut debug = false;
                        if let Some(ref debug_fn) = self.config.debug_fn {
                            if func.func_name.contains(debug_fn) {
                                debug = true;
                            }
                        }
                        let (violation, (src_bounding_lt, tgt_bounding_lt)) =
                            checks::arg_return_mut(
                                &src_ty,
                                &tgt_ty,
                                &bounds,
                                self.config.clone(),
                                debug,
                            );

                        if violation {
                            let source_place: Option<Place> =
                                get_mir_value_from_hir_param(&func.params[inp_num], &func.mir_body);
                            if source_place.is_none() {
                                continue;
                            }
                            let source_place = source_place.unwrap();

                            let dataflow_detected: bool;

                            if self.config.no_mir {
                                dataflow_detected = true;
                            } else if self.config.alias_analysis {
                                dataflow_detected = alias_analyzer.check_alias(
                                    &source_place.local,
                                    &src_ty.projection,
                                    &Local::from_usize(0),
                                    &tgt_ty.projection,
                                    false,
                                );
                                alias_analyzer.reset();
                            } else {
                                taint_analyzer.mark_taint(&source_place.local, source_field, false);
                                dataflow_detected =
                                    taint_analyzer.check_taint(&Local::from_usize(0), target_field);
                            }
                            if dataflow_detected {
                                let (html, markdown) = arg_return_mut_report(
                                    self.tcx,
                                    &func,
                                    inp_num,
                                    src_ty,
                                    tgt_ty,
                                    src_bounding_lt,
                                    tgt_bounding_lt,
                                );

                                return Some(Report {
                                    html,
                                    markdown,
                                    func_name: String::new(),
                                    error_type: "uaf".to_string(),
                                    queries: Vec::new(),
                                });
                            }
                            taint_analyzer.clear_taint();
                        }
                    }
                }
            }
        }
        None
    }

    fn check_arg_arg_violations<'a>(&self, func: &MirFunc<'tcx, 'a>) -> Option<Report> {
        let mut taint_analyzer = TaintAnalyzer::new(&func.mir_body, self.config.clone());
        let mut alias_analyzer = AliasAnalyzer::new(&func.mir_body, self.config.clone());

        for (inp_num1, inp1) in func.fn_sig.decl.inputs.iter().enumerate() {
            let inp1_subtypes = get_sub_types(inp1, &func.generic_bounds, self.tcx);
            let bounds1 = get_implicit_lifetime_bounds(inp1, &func.generic_bounds, self.tcx);

            for (inp_num2, inp2) in func.fn_sig.decl.inputs.iter().enumerate() {
                if inp_num1 == inp_num2 {
                    continue;
                }

                let inp2_subtypes = get_sub_types(inp2, &func.generic_bounds, self.tcx);
                let mut bounds2 =
                    get_implicit_lifetime_bounds(inp2, &func.generic_bounds, self.tcx);

                bounds2.append(&mut bounds1.clone());
                bounds2.append(&mut func.lifetime_bounds.clone());

                for src_ty in inp1_subtypes.iter() {
                    for tgt_ty in inp2_subtypes.iter() {
                        if self.config.generic_matches_all {
                            // def_id `None` matches everything
                            if src_ty.def_id.is_some()
                                && tgt_ty.def_id.is_some()
                                && (src_ty.def_id != tgt_ty.def_id)
                                && (!src_ty.is_closure)
                                && (!tgt_ty.is_closure)
                            {
                                continue;
                            }
                        } else {
                            // def_id `None` only matches `None`
                            if src_ty.def_id != tgt_ty.def_id
                                && (!src_ty.is_closure)
                                && (!tgt_ty.is_closure)
                            {
                                continue;
                            }
                        }
                        let mut debug = false;
                        if let Some(ref debug_fn) = self.config.debug_fn {
                            if func.func_name.contains(debug_fn) {
                                debug = true;
                            }
                        }
                        let (violation, (src_bounding_lt, tgt_bounding_lt)) =
                            checks::arg_arg_outlives(
                                &src_ty,
                                &tgt_ty,
                                &bounds2,
                                self.config.clone(),
                                debug,
                            );
                        if violation {
                            let source_place: Option<Place> = get_mir_value_from_hir_param(
                                &func.params[inp_num1],
                                &func.mir_body,
                            );
                            if source_place.is_none() {
                                continue;
                            }
                            let source_place = source_place.unwrap();
                            let target_place: Option<Place> = get_mir_value_from_hir_param(
                                &func.params[inp_num2],
                                &func.mir_body,
                            );
                            if target_place.is_none() {
                                continue;
                            }
                            let target_place = target_place.unwrap();
                            let source_field = get_first_field(&src_ty.projection);
                            let target_field = get_first_field(&tgt_ty.projection);

                            let dataflow_detected: bool;

                            if self.config.no_mir {
                                dataflow_detected = true;
                            } else if self.config.alias_analysis {
                                dataflow_detected = alias_analyzer.check_alias(
                                    &source_place.local,
                                    &src_ty.projection,
                                    &target_place.local,
                                    &tgt_ty.projection,
                                    false,
                                );
                                alias_analyzer.reset();
                            } else {
                                taint_analyzer.mark_taint(&source_place.local, source_field, false);
                                dataflow_detected =
                                    taint_analyzer.check_taint(&target_place.local, target_field);
                            }

                            if dataflow_detected {
                                let (html, markdown) = arg_arg_uaf_report(
                                    self.tcx,
                                    &func,
                                    inp_num1,
                                    inp_num2,
                                    src_ty,
                                    tgt_ty,
                                    src_bounding_lt,
                                    tgt_bounding_lt,
                                );
                                let mut queries: Vec<String> = Vec::new();
                                let arg_name1 =
                                    get_name_from_param(&func.params[inp_num1]).unwrap();
                                queries.push(generate_llm_query(
                                    self.tcx,
                                    arg_name1.to_string(),
                                    get_actual_type(inp1, self.tcx).span,
                                    src_ty,
                                ));
                                // if tgt_ty.in_struct && tgt_is_raw {
                                //     queries.push(generate_llm_query(self.tcx, "ret".to_string(), ret_type.span, tgt_ty));
                                // }
                                return Some(Report {
                                    html,
                                    markdown,
                                    func_name: String::new(),
                                    error_type: "uaf".to_string(),
                                    queries,
                                });
                            }
                            taint_analyzer.clear_taint();
                        }
                    }
                }
            }
        }
        None
    }

    pub fn analyze(mut self) {
        println!("Logging reports to {}", self.config.report_dir.clone());

        let mut reports: Vec<Report> = Vec::new();

        for mirfunc in fn_iter(&self.tcx, self.config.clone()) {
            // We don't need to check unsafe functions
            if mirfunc.fn_sig.header.safety == rustc_hir::HeaderSafety::SafeTargetFeatures
                || mirfunc.fn_sig.header.safety
                    == rustc_hir::HeaderSafety::Normal(rustc_hir::Safety::Safe)
            {
                continue;
            }
            let mut fname = mirfunc.func_name.clone();
            if fname.contains("::") {
                fname = fname.split("::").last().unwrap().to_string();
            }
            println!("Func name: {:?}", &mirfunc.func_name);
            if self.config.shallow_filter {
                // Shallow filters for common patterns of false positives in trait implementations
                if fname == "clone" || mirfunc.impl_trait == "Clone" {
                    continue;
                }
                if mirfunc.impl_trait.contains("Iterator")
                    && ((fname == "next") || (fname == "next_back"))
                {
                    continue;
                }
            }
            if let Some(ref debug_fn) = self.config.debug_fn {
                if mirfunc.func_name.contains(debug_fn) {
                    println!("Func name: {:?}", &mirfunc.func_name);
                    self.debug_output(&mirfunc);
                }
            }
            let mut report = self.check_arg_return_violations(&mirfunc);
            if let Some(mut report) = report {
                report.func_name = fname.clone();
                reports.push(report);
            }

            let mut report = self.check_arg_arg_violations(&mirfunc);
            if let Some(mut report) = report {
                report.func_name = fname.clone();
                reports.push(report);
            }
        }

        if reports.len() == 0 {
            progress_info!("Found no errors");
            return;
        }

        fs::remove_dir_all(self.config.report_dir.as_str());
        fs::create_dir_all(self.config.report_dir.as_str());

        let mut name_repeat_count: HashMap<String, u32> = HashMap::new();

        for report in reports.iter() {
            let mut folder_name: String = format!(
                "{}/{}-{}",
                self.config.report_dir.clone(),
                report.func_name,
                report.error_type
            );

            match name_repeat_count.get_mut(&folder_name) {
                Some(count) => {
                    folder_name = format!(
                        "{}/{}-{}-{}",
                        self.config.report_dir.clone(),
                        report.func_name,
                        report.error_type,
                        count
                    );
                    *count += 1;
                }
                None => {
                    name_repeat_count.insert(folder_name.clone(), 1 as u32);
                }
            }

            fs::create_dir(&folder_name);
            let html_report_filename: String = folder_name.clone() + "/report.html";
            let markdown_report_filename: String = folder_name.clone() + "/report.md";

            match fs::write(&html_report_filename, &report.html) {
                Ok(_) => progress_info!("Wrote report to {}", html_report_filename),
                Err(_) => progress_warn!("Could not write report to {}", html_report_filename),
            }
            match fs::write(&markdown_report_filename, &report.markdown) {
                Ok(_) => progress_info!("Wrote report to {}", markdown_report_filename),
                Err(_) => progress_warn!("Could not write report to {}", markdown_report_filename),
            }

            for (i, query) in report.queries.iter().enumerate() {
                let query_filename: String = folder_name.clone() + &format!("/query{i}.md");
                fs::write(&query_filename, query);
            }
        }
        progress_info!(
            "Found {} lifetime annotation bugs. Detailed reports can be found in {}",
            reports.len(),
            self.config.report_dir.clone()
        );
    }
}
