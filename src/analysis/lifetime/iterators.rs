use crate::analysis::lifetime::utils::{
    get_bounds_from_generics, get_defid_args_from_kind, get_lifetime_lifetime_bounds,
    get_mir_fn_from_defid,
};
use crate::analysis::lifetime::MirFunc;
use crate::YugaConfig;

use rustc_hir::{Item, OwnerNode};
use rustc_middle::bug;
use rustc_middle::ty::TyCtxt;

pub struct FnIter<'tcx, 'a> {
    items: Vec<&'a Item<'tcx>>,
    tcx: &'a TyCtxt<'tcx>,
    ind: usize,
    impl_ind: usize,
    config: YugaConfig,
}

pub fn fn_iter<'a, 'tcx>(tcx: &'a TyCtxt<'tcx>, config: YugaConfig) -> FnIter<'tcx, 'a> {
    let mut items: Vec<&rustc_hir::Item> = Vec::new();

    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = match tcx.expect_hir_owner_node(item_id.owner_id.def_id) {
            OwnerNode::Item(item) => item,
            _ => bug!("expected item, found"),
        };

        if let rustc_hir::ItemKind::Fn {
            ident: _,
            sig: _,
            generics: _,
            body: _,
            has_body: _,
        } = &item.kind
        {
            items.push(&item);
        }
        if let rustc_hir::ItemKind::Impl(this_impl) = &item.kind {
            items.push(&item);
        }
    }

    FnIter {
        items,
        tcx,
        ind: 0,
        impl_ind: 0,
        config,
    }
}

impl<'tcx, 'a> Iterator for FnIter<'tcx, 'a> {
    type Item = MirFunc<'tcx, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ind >= self.items.len() {
            return None;
        }

        let item: &Item = self.items[self.ind];

        match &item.kind {
            rustc_hir::ItemKind::Fn {
                sig,
                generics,
                body,
                ..
            } => {
                // So weird, but looks like the HIR doesn't contain the visibility directly
                // Only as a span into the source file
                let source_map = self.tcx.sess.source_map();
                let vis_string = source_map
                    .span_to_snippet(item.vis_span)
                    .unwrap_or_else(|e| format!("unable to get source: {:?}", e));
                if self.config.pub_only && (vis_string != "pub") {
                    self.ind += 1;
                    return self.next();
                }

                let params = self.tcx.hir_body(*body).params;
                let body_span = self.tcx.hir_body(*body).value.span;
                let func_name = format!("{:?}", item);
                let impl_trait = "".to_string();
                let generic_bounds = get_bounds_from_generics(&generics);
                let lifetime_bounds = get_lifetime_lifetime_bounds(&generics);
                let body_defid = self
                    .tcx
                    .parent_hir_node(body.hir_id)
                    .associated_body()
                    .unwrap()
                    .0;
                let mir_body = get_mir_fn_from_defid(self.tcx, body_defid.to_def_id()).unwrap();

                let mirfunc = MirFunc {
                    fn_sig: sig,
                    body_span: body_span,
                    func_name: func_name,
                    impl_trait: impl_trait,
                    params: params,
                    generic_bounds: generic_bounds,
                    lifetime_bounds: lifetime_bounds,
                    mir_body: mir_body,
                };
                self.ind += 1;
                return Some(mirfunc);
            }

            rustc_hir::ItemKind::Impl(this_impl) => {
                if self.impl_ind >= this_impl.items.len() {
                    self.impl_ind = 0;
                    self.ind += 1;
                    return self.next();
                }

                let impl_item = &this_impl.items[self.impl_ind];
                self.impl_ind += 1;

                if let rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
                    kind: rustc_hir::ImplItemKind::Fn(fn_sig, body_id),
                    generics,
                    vis_span,
                    ..
                }) = self.tcx.hir_node_by_def_id(impl_item.id.owner_id.def_id)
                {
                    let source_map = self.tcx.sess.source_map();
                    let vis_string = source_map
                        .span_to_snippet(*vis_span)
                        .unwrap_or_else(|e| format!("unable to get source: {:?}", e));

                    // Need to look up the type associated with this impl
                    let (def_id, _) = get_defid_args_from_kind(&this_impl.self_ty.kind);
                    let mut type_vis = "".to_string();
                    if let Some(def_id) = def_id {
                        let span = self.tcx.hir_span_if_local(def_id);
                        if let Some(span) = span {
                            type_vis = source_map
                                .span_to_snippet(span)
                                .unwrap_or_else(|e| format!("unable to get source: {:?}", e));
                        }
                    }

                    // Impl of pub traits of a public type are public even if not specified
                    let is_trait_impl = this_impl.of_trait.is_some();
                    if self.config.pub_only
                        && (vis_string != "pub")
                        && !(is_trait_impl && type_vis == "pub")
                    {
                        return self.next();
                    }

                    let mut impl_trait = "".to_string();

                    if let Some(trait_ref) = &this_impl.of_trait {
                        impl_trait = source_map
                            .span_to_snippet(trait_ref.path.span)
                            .unwrap_or_else(|e| format!("unable to get source: {:?}", e));
                    }

                    let mut self_lifetimes: Vec<rustc_hir::LifetimeName> = Vec::new();

                    let impl_generic_bounds = get_bounds_from_generics(&this_impl.generics);
                    let impl_lifetime_bounds = get_lifetime_lifetime_bounds(&this_impl.generics);

                    let params = self.tcx.hir_body(*body_id).params;
                    let body_defid = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                    let body_span = self.tcx.hir_body(*body_id).value.span;

                    let mut func_name: String = "".to_owned();

                    if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                        this_impl.self_ty.kind
                    {
                        func_name = format!("{:?}::{}", path.res, impl_item.ident.name.as_str());
                    }

                    let mut generic_bounds = get_bounds_from_generics(&generics);
                    let mut lifetime_bounds = get_lifetime_lifetime_bounds(&generics);

                    generic_bounds.extend(&impl_generic_bounds);
                    lifetime_bounds.extend(&impl_lifetime_bounds);

                    let mir_body = get_mir_fn_from_defid(self.tcx, body_defid).unwrap();

                    let mirfunc = MirFunc {
                        fn_sig: fn_sig,
                        body_span: body_span,
                        func_name: func_name,
                        impl_trait: impl_trait,
                        params: params,
                        generic_bounds: generic_bounds,
                        lifetime_bounds: lifetime_bounds,
                        mir_body: mir_body,
                    };

                    return Some(mirfunc);
                }
                return self.next();
            }
            _ => {
                self.impl_ind = 0;
                self.ind += 1;
                return self.next();
            }
        }
    }
}
