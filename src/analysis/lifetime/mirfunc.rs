use rustc_hash::FxHashMap;
use rustc_hir::LifetimeKind;
use rustc_hir::{def_id::DefId, FnSig, Param};
use rustc_span::Span;

use rustc_middle::mir::Body;
pub struct MirFunc<'tcx, 'a> {
    pub fn_sig: &'a FnSig<'tcx>,
    pub body_span: Span,
    pub func_name: String,
    pub impl_trait: String,
    pub params: &'a [Param<'tcx>],
    pub generic_bounds: FxHashMap<DefId, rustc_hir::GenericBounds<'tcx>>,
    pub lifetime_bounds: Vec<(LifetimeKind, LifetimeKind)>,
    pub mir_body: &'a Body<'tcx>,
}
