use rustc_hir::LifetimeName;
use rustc_hir::{def_id::DefId, FnSig, Param};
use rustc_span::Span;

use rustc_middle::mir::Body;
use std::collections::HashMap;

pub struct MirFunc<'tcx, 'a> {
    pub fn_sig: &'a FnSig<'tcx>,
    pub body_span: Span,
    pub func_name: String,
    pub impl_trait: String,
    pub params: &'a [Param<'tcx>],
    pub generic_bounds: HashMap<DefId, rustc_hir::GenericBounds<'tcx>>,
    pub lifetime_bounds: Vec<(LifetimeName, LifetimeName)>,
    pub mir_body: &'a Body<'tcx>,
}
