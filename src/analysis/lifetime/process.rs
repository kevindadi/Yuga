use rustc_hash::FxHashMap;
use rustc_hir::{def_id::DefId, Lifetime, LifetimeKind, Mutability, Ty, TyKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use std::cmp::Eq;
use std::hash::Hash;
use std::marker::Copy;

use crate::analysis::lifetime::utils::{
    check_if_closure, compare_lifetimes, get_bounds_from_generics, FieldInfo,
    MyProjection::{self, MyDeref, MyField},
};

/*
    If we have something like
    ```
    fn foo(x: T)
        where T: 'a + 'b
    ```
    then we want to get `['a, 'b]`, given `T`.
*/
pub fn get_trait_lifetime_bounds<'tcx>(
    def_id: &DefId,
    trait_bounds: &FxHashMap<DefId, rustc_hir::GenericBounds<'tcx>>,
) -> Vec<LifetimeKind> {
    let mut lifetimes: Vec<LifetimeKind> = Vec::new();

    if trait_bounds.contains_key(&def_id) {
        for bound in *trait_bounds.get(def_id).unwrap() {
            if let rustc_hir::GenericBound::Outlives(Lifetime { kind, .. }) = *bound {
                lifetimes.push(*kind);
            }
        }
    }
    lifetimes
}

#[derive(Debug, Clone)]
pub struct MyLifetime {
    pub names: Vec<LifetimeKind>,
    pub is_mut: bool,
    pub is_raw: bool,
    pub is_refcell: bool,
}

#[derive(Debug, Clone)]
pub struct ShortLivedType {
    pub def_id: Option<DefId>,
    pub type_span: Span,
    pub lifetimes: Vec<MyLifetime>,
    // How to reach this type from the container type? Deref, field.
    pub projection: Vec<MyProjection>,

    pub in_struct: bool,  // Is it inside a structure?
    pub is_closure: bool, // Is it a closure?
}

fn apply_remap<T>(x: T, remap: &FxHashMap<T, T>) -> T
where
    T: Hash + Eq + Copy,
{
    if remap.contains_key(&x) {
        *(remap.get(&x).unwrap())
    } else {
        x
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LifetimeKindWrapper(pub LifetimeKind);

impl Hash for LifetimeKindWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self.0 {
            LifetimeKind::Static => {
                0.hash(state);
            }
            LifetimeKind::Param(def_id) => {
                1.hash(state);
                def_id.hash(state);
            }
            LifetimeKind::ImplicitObjectLifetimeDefault => {
                2.hash(state);
            }
            LifetimeKind::Error => {
                3.hash(state);
            }
            LifetimeKind::Infer => {
                4.hash(state);
            }
        }
    }
}

/*
    "This type contains all these other subtypes that live at least as long as ___"
*/
pub fn get_sub_types<'tcx>(
    ty: &'tcx Ty<'tcx>,
    trait_bounds: &FxHashMap<DefId, rustc_hir::GenericBounds<'tcx>>,
    tcx: &'tcx TyCtxt<'tcx>,
) -> Vec<ShortLivedType> {
    get_sub_types_dbg(
        ty,
        trait_bounds,
        tcx,
        Vec::new(),
        FxHashMap::default(),
        FxHashMap::default(),
        false,
    )
}

pub fn get_sub_types_dbg<'tcx>(
    ty: &'tcx Ty<'tcx>,
    trait_bounds: &FxHashMap<DefId, rustc_hir::GenericBounds<'tcx>>,
    tcx: &'tcx TyCtxt<'tcx>,
    mut known_defids: Vec<DefId>, // Needed to prevent infinite loop
    mut defid_remap: FxHashMap<DefId, &'tcx Ty<'tcx>>,
    mut lifetime_remap: FxHashMap<LifetimeKindWrapper, LifetimeKindWrapper>,
    debug: bool,
) -> Vec<ShortLivedType> {
    let mut types: Vec<ShortLivedType> = Vec::new();

    match &ty.kind {
        TyKind::Ptr(mut_ty) => {
            let sub_types = get_sub_types_dbg(
                &mut_ty.ty,
                trait_bounds,
                tcx,
                known_defids.clone(),
                defid_remap.clone(),
                lifetime_remap.clone(),
                debug,
            );
            let is_mut: bool = (mut_ty.mutbl == Mutability::Mut);
            let this_lifetime = MyLifetime {
                names: Vec::new(),
                is_mut: (mut_ty.mutbl == Mutability::Mut),
                is_raw: true,
                is_refcell: false,
            };
            for sub_type in sub_types.iter() {
                let mut temp = sub_type.clone();
                temp.projection.insert(0 as usize, MyDeref);
                temp.lifetimes.insert(0 as usize, this_lifetime.clone());
                types.push(temp);
            }
        }

        TyKind::Ref(lifetime, rustc_hir::MutTy { ty: sub_ty, mutbl }) => {
            // Straight away do a substitution if available
            let lifetime_name = lifetime.kind;
            // This will do its own lifetime substitution so we don't need to substitute again!
            let sub_types = get_sub_types_dbg(
                &sub_ty,
                trait_bounds,
                tcx,
                known_defids.clone(),
                defid_remap.clone(),
                lifetime_remap.clone(),
                debug,
            );

            let this_lifetime = MyLifetime {
                names: Vec::from([lifetime_name]),
                is_mut: (*mutbl == Mutability::Mut),
                is_raw: false,
                is_refcell: false,
            };
            for sub_type in sub_types.iter() {
                let mut temp = sub_type.clone();
                temp.projection.insert(0 as usize, MyDeref);
                temp.lifetimes.insert(0 as usize, this_lifetime.clone());
                types.push(temp);
            }
        }

        TyKind::Slice(sub_ty) | TyKind::Array(sub_ty, _) => {
            // We don't handle array indices (we probably should, eventually).
            let mut sub_types = get_sub_types_dbg(
                &sub_ty,
                trait_bounds,
                tcx,
                known_defids.clone(),
                defid_remap.clone(),
                lifetime_remap.clone(),
                debug,
            );
            types.append(&mut sub_types);
        }

        TyKind::Tup(arg_slice) => {
            // This is the weird type `()`
            // It has no def_id.
            if arg_slice.len() == 0 {
                types.push(ShortLivedType {
                    def_id: None,
                    type_span: ty.span,
                    lifetimes: Vec::new(),
                    projection: Vec::new(),
                    in_struct: false,
                    is_closure: false,
                });
            }

            for (i, sub_ty) in arg_slice.iter().enumerate() {
                let sub_types = get_sub_types_dbg(
                    &sub_ty,
                    trait_bounds,
                    tcx,
                    known_defids.clone(),
                    defid_remap.clone(),
                    lifetime_remap.clone(),
                    debug,
                );
                for sub_type in sub_types.iter() {
                    let mut temp = sub_type.clone();
                    temp.projection.insert(
                        0 as usize,
                        MyField(FieldInfo {
                            field_num: i as usize,
                            field_name: None,
                            type_span: None,
                            struct_decl_span: None,
                            struct_def_id: None,
                        }),
                    );
                    types.push(temp);
                }
            }
        }

        // Primitive type
        TyKind::Path(rustc_hir::QPath::Resolved(
            _,
            rustc_hir::Path {
                res: rustc_hir::def::Res::PrimTy(_),
                ..
            },
        )) => {
            types.push(ShortLivedType {
                def_id: None,
                type_span: ty.span,
                lifetimes: Vec::new(),
                projection: Vec::new(),
                in_struct: false,
                is_closure: false,
            });
        }

        // A path to something with a def_id
        TyKind::Path(rustc_hir::QPath::Resolved(
            _,
            rustc_hir::Path {
                res: rustc_hir::def::Res::Def(_, def_id),
                segments,
                ..
            },
        )) => {
            // Straight away, do a substitution if one is available
            if defid_remap.contains_key(def_id) {
                let new_ty: &Ty = defid_remap.get(def_id).unwrap();
                // We're done here
                return get_sub_types_dbg(
                    new_ty,
                    trait_bounds,
                    tcx,
                    known_defids.clone(),
                    defid_remap.clone(),
                    lifetime_remap.clone(),
                    debug,
                );
            }

            let def_str: String = format!("{:?}", def_id);
            let def_name: String = def_str[..(def_str.len() - 1)]
                .split("::")
                .last()
                .unwrap()
                .to_string();

            if def_name == "PhantomData" {
                return types;
            }
            /*
            This is an owned type, so push this def_id with no lifetime arguments
            */
            types.push(ShortLivedType {
                def_id: Some(*def_id),
                type_span: ty.span,
                lifetimes: Vec::new(),
                projection: Vec::new(),
                in_struct: false,
                is_closure: false,
            });

            // This is a generic
            if trait_bounds.contains_key(&def_id) {
                let lifetimes = get_trait_lifetime_bounds(&def_id, trait_bounds);

                if debug {
                    println!("Trait bounds: {:?}", trait_bounds.get(&def_id).unwrap());
                }

                let is_closure = {
                    if check_if_closure(&trait_bounds.get(&def_id).unwrap()) {
                        true
                    } else {
                        false
                    }
                };
                if !lifetimes.contains(&LifetimeKind::Static) {
                    // T could be a borrow - T ~ &S
                    // Create a new lifetime with the def_id of the generic T
                    let artificial = LifetimeKind::Param(rustc_hir::def_id::LocalDefId {
                        local_def_index: def_id.index,
                    });
                    let this_lifetime = MyLifetime {
                        names: Vec::from([artificial]),
                        is_mut: false, // Could be true also... TODO
                        is_raw: false,
                        is_refcell: false,
                    };
                    types.push(ShortLivedType {
                        def_id: None,
                        type_span: ty.span,
                        lifetimes: Vec::from([this_lifetime]),
                        projection: Vec::from([MyDeref]),
                        in_struct: false,
                        is_closure: is_closure,
                    });
                }
                return types; // We're finished here
            }
            // ------------------------------------------------

            // Okay, so now it's not a generic. Moving on.
            // Get its lifetime and type parameters specified inside <.>

            let mut struct_lifetimes: Vec<LifetimeKind> = Vec::new();
            let mut type_parameters: Vec<&Ty> = Vec::new();

            // let temp : Vec<rustc_hir::GenericArg> = Vec::new();
            let mut actual_args: Vec<&rustc_hir::GenericArg> = Vec::new(); // Placeholder

            if let Some(rustc_hir::PathSegment {
                args: Some(rustc_hir::GenericArgs { args, .. }),
                ..
            }) = segments.last()
            {
                // actual_args = args;

                for arg in *args {
                    actual_args.push(arg);

                    if let rustc_hir::GenericArg::Lifetime(rustc_hir::Lifetime { kind, .. }) = *arg
                    {
                        // Apply the remap here immediately
                        struct_lifetimes.push(*kind);
                    }
                    if let rustc_hir::GenericArg::Type(ty) = arg {
                        type_parameters.push(ty.as_unambig_ty());
                    }
                }
            }
            // ------------------------------------------------
            // Now if it's a structure, try to get the definition

            let node = def_id.as_local().map(|id| tcx.hir_node_by_def_id(id));

            if node.is_none() || known_defids.contains(&def_id) {
                // Non-local def, we weren't able to locate definition
                // Could be something like Vec or Option too
                // Just iterate through its type arguments then
                // Also - could be something we've already visited

                known_defids.push(*def_id); // I'm not sure but just add it again anyway, can't hurt

                for &ty_param in type_parameters.iter() {
                    if debug {
                        println!("{:?}", ty_param);
                    }
                    let sub_types = get_sub_types_dbg(
                        ty_param,
                        trait_bounds,
                        tcx,
                        known_defids.clone(),
                        defid_remap.clone(),
                        lifetime_remap.clone(),
                        debug,
                    );

                    for sub_type in sub_types.iter() {
                        let mut temp_type = sub_type.clone();
                        temp_type.projection.insert(
                            0 as usize,
                            MyField(FieldInfo {
                                field_num: 0 as usize,
                                field_name: None,
                                type_span: None,
                                struct_decl_span: None,
                                struct_def_id: Some(*def_id),
                            }),
                        ); // Assume that this type is at index 0

                        if def_name == "RefCell" {
                            let ref_lifetime = MyLifetime {
                                names: Vec::new(),
                                is_mut: false,
                                is_raw: false,
                                is_refcell: true,
                            };
                            temp_type.lifetimes.insert(0 as usize, ref_lifetime);
                        }

                        if struct_lifetimes.len() != 0 {
                            for (i, lt) in temp_type.lifetimes.iter().enumerate() {
                                if lt.is_refcell {
                                    continue;
                                }
                                // Pick out the first non-refcell lifetime. Check if it's raw and has no existing lifetimes
                                if lt.is_raw && (lt.names.len() == 0) {
                                    temp_type.lifetimes[i].names = struct_lifetimes.clone();
                                }
                                break;
                            }
                        }
                        types.push(temp_type);
                    }
                }
                if debug {
                    println!("Returning the following types :");
                    println!("{:#?}", types);
                    println!("\n\n");
                }
                return types;
                // We're done here
            }

            known_defids.push(*def_id);

            // ------------------------------------------------
            // We managed to find the structure definition. Go through sub-fields

            if let Some(rustc_hir::Node::Item(rustc_hir::Item {
                kind: rustc_hir::ItemKind::Struct(ident, generics, variant_data),
                span: struct_decl_span,
                ..
            })) = node
            {
                let mut new_trait_bounds = get_bounds_from_generics(generics);
                new_trait_bounds.extend(
                    trait_bounds
                        .into_iter()
                        .map(|(k, v)| (k.clone(), v.clone())),
                );

                let (mut new_lifetime_remap, mut new_defid_remap) =
                    generate_remappings(generics.params, actual_args);
                // This is annoying, but the types in `actual_args` need to be remapped too.
                // Rather than iterate through them and remap each one, we generate the remapping,
                // and then remap the remapping.
                // https://knowyourmeme.com/memes/xzibit-yo-dawg
                // new_defid_remap 	= new_defid_remap.iter()
                // 									.map(|(&x, &y)| (x, apply_remap(y, &defid_remap)))
                // 									.collect();
                // Is this necessary? Can't hurt anyway
                new_lifetime_remap = new_lifetime_remap
                    .iter()
                    .map(|(&x, &y)| (x, apply_remap(y, &lifetime_remap)))
                    .collect();
                lifetime_remap.extend(new_lifetime_remap);
                defid_remap.extend(new_defid_remap);

                for (i, field) in variant_data.fields().iter().enumerate() {
                    let sub_types = get_sub_types_dbg(
                        &field.ty,
                        &new_trait_bounds,
                        tcx,
                        known_defids.clone(),
                        defid_remap.clone(),
                        lifetime_remap.clone(),
                        debug,
                    );

                    for sub_type in sub_types.iter() {
                        let mut temp_type = sub_type.clone();
                        let field_name: String = field.ident.name.as_str().to_string();
                        temp_type.projection.insert(
                            0 as usize,
                            MyField(FieldInfo {
                                field_num: i as usize,
                                field_name: Some(field_name),
                                type_span: Some(field.ty.span),
                                struct_decl_span: Some(*struct_decl_span),
                                struct_def_id: Some(*def_id),
                            }),
                        );
                        temp_type.in_struct = true;

                        if struct_lifetimes.len() != 0 {
                            for (i, lt) in temp_type.lifetimes.iter().enumerate() {
                                if lt.is_refcell {
                                    continue;
                                }
                                // Pick out the first non-refcell lifetime. Check if it's raw.
                                // If it has no existing lifetimes, replace it with the structure lifetimes.
                                if lt.is_raw && (lt.names.len() == 0) {
                                    temp_type.lifetimes[i].names = struct_lifetimes.clone();
                                }
                                break;
                            }
                        }
                        types.push(temp_type);
                    }
                }
            }
        }

        // A path which is an alias for self
        TyKind::Path(rustc_hir::QPath::Resolved(
            _,
            rustc_hir::Path {
                res:
                    rustc_hir::def::Res::SelfTyAlias {
                        alias_to: impl_def_id,
                        ..
                    },
                ..
            },
        )) => {
            if debug {
                println!("Impl def id: {:?}", impl_def_id);
            }
            let impl_node = impl_def_id.as_local().map(|id| tcx.hir_node_by_def_id(id));

            if let Some(rustc_hir::Node::Item(rustc_hir::Item {
                kind:
                    rustc_hir::ItemKind::Impl(rustc_hir::Impl {
                        self_ty, generics, ..
                    }),
                ..
            })) = impl_node
            {
                let mut new_trait_bounds = get_bounds_from_generics(generics);
                new_trait_bounds.extend(
                    trait_bounds
                        .into_iter()
                        .map(|(k, v)| (k.clone(), v.clone())),
                );

                let mut sub_types = get_sub_types_dbg(
                    &self_ty,
                    &new_trait_bounds,
                    tcx,
                    known_defids.clone(),
                    defid_remap.clone(),
                    lifetime_remap.clone(),
                    debug,
                );
                types.append(&mut sub_types);
            }
        }
        _ => (),
    }
    if debug {
        println!("Returning the following types :");
        println!("{:#?}", types);
        println!("\n\n");
    }
    types
}

fn generate_remappings<'tcx>(
    formal_args: &'tcx [rustc_hir::GenericParam<'tcx>],
    actual_args: Vec<&'tcx rustc_hir::GenericArg<'tcx>>,
) -> (
    FxHashMap<LifetimeKindWrapper, LifetimeKindWrapper>,
    FxHashMap<DefId, &'tcx Ty<'tcx>>,
) {
    let mut lifetime_remap: FxHashMap<LifetimeKindWrapper, LifetimeKindWrapper> =
        FxHashMap::default();
    let mut defid_remap: FxHashMap<DefId, &'tcx Ty<'tcx>> = FxHashMap::default();

    if actual_args.len() != formal_args.len() {
        return (lifetime_remap, defid_remap);
    }

    for (i, f_arg) in formal_args.iter().enumerate() {
        let a_arg = &actual_args[i];

        if let rustc_hir::GenericParamKind::Type { .. } = f_arg.kind {
            match a_arg {
                rustc_hir::GenericArg::Type(ty) => {
                    defid_remap.insert(f_arg.def_id.to_def_id(), ty.as_unambig_ty());
                }
                _ => {
                    panic!("Formal arg is a type but actual arg is not");
                }
            }
            continue;
        }
        if let rustc_hir::GenericParamKind::Lifetime { .. } = f_arg.kind {
            match a_arg {
                rustc_hir::GenericArg::Lifetime(a_lifetime) => {
                    let f_lifetime = LifetimeKind::Param(f_arg.def_id);
                    lifetime_remap.insert(
                        LifetimeKindWrapper(f_lifetime),
                        LifetimeKindWrapper(a_lifetime.kind),
                    );
                }
                _ => {
                    panic!("Formal arg is a lifetime but actual arg is not");
                }
            }
        }
    }
    (lifetime_remap, defid_remap)
}

pub fn get_implicit_lifetime_bounds<'tcx>(
    ty: &'tcx Ty<'tcx>,
    trait_bounds: &FxHashMap<DefId, rustc_hir::GenericBounds<'tcx>>,
    tcx: &'tcx TyCtxt<'tcx>,
) -> Vec<(LifetimeKind, LifetimeKind)> {
    let sub_types = get_sub_types(ty, trait_bounds, tcx);
    let mut all_bounds: Vec<(LifetimeKind, LifetimeKind)> = Vec::new();

    for sub_type in sub_types.iter() {
        for i in 0..sub_type.lifetimes.len() {
            for j in (i + 1)..sub_type.lifetimes.len() {
                if (sub_type.lifetimes[i].names.len() > 0)
                    && (sub_type.lifetimes[j].names.len() > 0)
                {
                    for x in sub_type.lifetimes[j].names.iter() {
                        // Notice that it's j and then i
                        for y in sub_type.lifetimes[i].names.iter() {
                            all_bounds.push((*x, *y));
                        }
                    }
                }
            }
        }
    }

    let mut unique_bounds: Vec<(LifetimeKind, LifetimeKind)> = Vec::new();

    for (x, y) in all_bounds.iter() {
        if !unique_bounds
            .iter()
            .any(|(a, b)| compare_lifetimes(&x, &a) && compare_lifetimes(&y, &b))
        {
            unique_bounds.push((*x, *y));
        }
    }
    unique_bounds
}
