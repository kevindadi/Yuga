use crate::analysis::lifetime::process::ShortLivedType;
use crate::analysis::lifetime::utils::{
    compare_lifetimes, get_drop_impl,
    MyProjection::{self},
};
use crate::YugaConfig;
use rustc_hir::LifetimeName;
use rustc_middle::ty::TyCtxt;

pub fn arg_return_outlives(
    source_type: &ShortLivedType,
    target_type: &ShortLivedType,
    lifetime_bounds: &Vec<(LifetimeName, LifetimeName)>,
    tcx: &TyCtxt<'_>,
    config: YugaConfig,
    debug: bool,
) -> (bool, (Vec<LifetimeName>, Vec<LifetimeName>), (bool, bool)) {
    let source_lifetimes = &source_type.lifetimes;
    let target_lifetimes = &target_type.lifetimes;

    let mut src_bounding_lt: Vec<LifetimeName> = Vec::new();
    let mut first = true;
    let mut src_is_raw = false;
    let mut src_needs_drop_impl = false;

    if debug {
        println!("Source lifetimes:\n{:?}", source_lifetimes);
        println!("Target_lifetimes:\n{:?}", target_lifetimes);
    }

    // The source lifetime is the one that is "closest" to the value
    // Note that this is a reverse iterator
    for src_lifetime in source_lifetimes.iter().rev().filter(|&x| !(x.is_refcell)) {
        // If the closest lifetime is a raw pointer, then we set src_is_raw = True
        if first && src_lifetime.is_raw {
            src_is_raw = true;
            if src_lifetime.names.len() == 0 {
                src_needs_drop_impl = true;
            }
        }
        first = false;

        if src_lifetime.names.len() > 0 {
            src_bounding_lt = src_lifetime.names.clone();
            break;
        }
    }
    // If there are no source lifetimes, then we own the thing
    // and we can assume it'll live forever. No violation possible.
    if (src_bounding_lt.len() == 0) || src_bounding_lt.contains(&LifetimeName::Static) {
        return (false, (Vec::new(), Vec::new()), (false, false));
    }

    let mut tgt_bounding_lt: Vec<LifetimeName> = Vec::new();
    let mut first = true;
    let mut tgt_is_raw = false;
    let mut tgt_needs_drop_impl = false;

    for tgt_lifetime in target_lifetimes.iter().rev().filter(|&x| !(x.is_refcell)) {
        if first && tgt_lifetime.is_raw {
            tgt_is_raw = true;
            if tgt_lifetime.names.len() == 0 {
                tgt_needs_drop_impl = true;
            }
        }
        first = false;

        if tgt_lifetime.names.len() > 0 {
            tgt_bounding_lt = tgt_lifetime.names.clone();
            break;
        }
    }
    if debug {
        println!("Source bounding lifetimes: {:?}", src_bounding_lt);
        println!("Target bounding lifetimes: {:?}", tgt_bounding_lt);
        println!("Source is raw: {:?}", src_is_raw);
        println!("Target is raw: {:?}", tgt_is_raw);
        println!("Source needs drop impl: {:?}", src_needs_drop_impl);
        println!("Target needs drop impl: {:?}", tgt_needs_drop_impl);
    }

    if (!src_is_raw) && (!tgt_is_raw) {
        return (false, (Vec::new(), Vec::new()), (false, false));
    }
    if (src_is_raw && (!source_type.in_struct)) || (tgt_is_raw && (!target_type.in_struct)) {
        return (false, (Vec::new(), Vec::new()), (false, false));
    }

    // If we are returning something that is neither a borrow nor raw pointer,
    // then this is not something we care about.
    if (tgt_bounding_lt.len() == 0) && !tgt_is_raw {
        return (false, (Vec::new(), Vec::new()), (false, false));
    }

    fn check_if_drop_impl_exists(ty: &ShortLivedType, tcx: &TyCtxt<'_>) -> bool {
        let mut break_point = 0;
        // Find the last Deref projection (corresponding to the raw pointer)
        for (i, proj) in ty.projection.iter().rev().enumerate() {
            if let _proj = MyProjection::MyDeref {
                break;
            }
            break_point = i;
        }
        // Start from the next index in reverse order, looking for a field projection
        for proj in ty.projection.iter().rev().skip(break_point + 1) {
            match proj {
                MyProjection::MyField(field_info) => {
                    // Get the def_id of the struct corresponding to that field projection
                    if let Some(struct_def_id) = field_info.struct_def_id {
                        if get_drop_impl(struct_def_id, tcx).is_some() {
                            return true;
                        }
                    }
                }
                // The moment you hit another deref, stop
                MyProjection::MyDeref => break,
            }
        }
        false
    }

    if config.filter_by_drop_impl {
        if src_needs_drop_impl {
            src_needs_drop_impl = !(check_if_drop_impl_exists(&source_type, &tcx));
        }
        if tgt_needs_drop_impl {
            tgt_needs_drop_impl = !(check_if_drop_impl_exists(&target_type, &tcx));
        }
        // If both of them are raw, and both don't have drop impl, then not a bug.
        if (src_is_raw && tgt_is_raw) && (src_needs_drop_impl && tgt_needs_drop_impl) {
            return (false, (Vec::new(), Vec::new()), (false, false));
        }
    }
    // If we've made it this far and you are transfering ownership to the receiver,
    // then that's a definite violation.
    if (tgt_bounding_lt.len() == 0) || tgt_bounding_lt.contains(&LifetimeName::Static) {
        return (
            true,
            (src_bounding_lt.clone(), tgt_bounding_lt.clone()),
            (false, false),
        );
    }
    // We have some set of source lifetimes and some set of target lifetimes.
    // This type could be associated with any of the source lifetimes.
    // Need to check if all the source lifetimes outlive any of the target lifetimes.
    for src_lt in src_bounding_lt.iter() {
        let mut flag = false;
        for tgt_lt in tgt_bounding_lt.iter() {
            if compare_lifetimes(src_lt, tgt_lt) {
                flag = true;
                break;
            } else {
                if lifetime_bounds
                    .iter() // Source should outlive the target
                    .any(|&(x, y)| compare_lifetimes(&x, &src_lt) && compare_lifetimes(&y, &tgt_lt))
                {
                    flag = true;
                    break;
                }
            }
        }
        // This source lifetime is not compatible with any of the target lifetimes
        if !flag {
            return (
                true,
                (Vec::from([*src_lt]), tgt_bounding_lt.clone()),
                (src_is_raw, tgt_is_raw),
            );
        }
    }
    (false, (Vec::new(), Vec::new()), (false, false))
}

pub fn arg_return_mut(
    source_type: &ShortLivedType,
    target_type: &ShortLivedType,
    lifetime_bounds: &Vec<(LifetimeName, LifetimeName)>,
    config: YugaConfig,
    debug: bool,
) -> (bool, (Vec<LifetimeName>, Vec<LifetimeName>)) {
    let source_lifetimes = &source_type.lifetimes;
    let target_lifetimes = &target_type.lifetimes;

    let mut src_bounding_lt: Vec<LifetimeName> = Vec::new();
    let mut first = true;
    let mut src_is_raw = false;

    for src_lifetime in source_lifetimes.iter().rev() {
        if src_lifetime.is_refcell {
            continue;
        }
        if first {
            if !src_lifetime.is_mut {
                return (false, (Vec::new(), Vec::new()));
            }
            src_is_raw = src_lifetime.is_raw;
            first = false;
            continue;
        }
        src_bounding_lt = src_lifetime.names.clone();
        break;
    }
    if (src_bounding_lt.len() == 0) || src_bounding_lt.contains(&LifetimeName::Static) {
        return (false, (Vec::new(), Vec::new()));
    }
    let mut tgt_is_raw = false;
    for tgt_lifetime in target_lifetimes.iter().rev() {
        if tgt_lifetime.is_refcell {
            continue;
        }
        tgt_is_raw = tgt_lifetime.is_raw;
        break;
    }
    let mut tgt_bounding_lt: Vec<LifetimeName> = Vec::new();
    for tgt_lifetime in target_lifetimes.iter() {
        if tgt_lifetime.is_refcell {
            continue;
        }
        if tgt_lifetime.names.len() > 0 {
            tgt_bounding_lt = tgt_lifetime.names.clone();
        }
    }
    if !(src_is_raw && source_type.in_struct) {
        return (false, (Vec::new(), Vec::new()));
    } // We want the source to be a raw pointer
    if tgt_is_raw {
        return (false, (Vec::new(), Vec::new()));
    } // We want the target to be a normal borrow
    if tgt_bounding_lt.len() == 0 {
        return (false, (Vec::new(), Vec::new()));
    }

    for src_lt in src_bounding_lt.iter() {
        let mut flag = false;
        for tgt_lt in tgt_bounding_lt.iter() {
            if compare_lifetimes(src_lt, tgt_lt) {
                flag = true;
                break;
            } else {
                if lifetime_bounds
                    .iter() // Source should outlive the target
                    .any(|&(x, y)| compare_lifetimes(&x, &src_lt) && compare_lifetimes(&y, &tgt_lt))
                {
                    flag = true;
                    break;
                }
            }
        }
        // This source lifetime is not compatible with any of the target lifetimes
        if !flag {
            return (true, (src_bounding_lt.clone(), tgt_bounding_lt.clone()));
        }
    }
    (false, (Vec::new(), Vec::new()))
}

pub fn arg_arg_outlives(
    source_type: &ShortLivedType,
    target_type: &ShortLivedType,
    lifetime_bounds: &Vec<(LifetimeName, LifetimeName)>,
    config: YugaConfig,
    debug: bool,
) -> (bool, (Vec<LifetimeName>, Vec<LifetimeName>)) {
    let source_lifetimes = &source_type.lifetimes;
    let target_lifetimes = &target_type.lifetimes;

    let mut src_bounding_lt: Vec<LifetimeName> = Vec::new();
    let mut first = true;
    let mut src_is_raw = false;

    // First get source bounding lifetime
    for src_lifetime in source_lifetimes.iter().rev() {
        if src_lifetime.is_refcell {
            continue;
        }
        if first && src_lifetime.is_raw {
            src_is_raw = true;
        }
        first = false;

        if src_lifetime.names.len() > 0 {
            src_bounding_lt = src_lifetime.names.clone();
            break;
        }
    }
    if src_bounding_lt.len() == 0 || src_bounding_lt.contains(&LifetimeName::Static) {
        return (false, (Vec::new(), Vec::new()));
    }

    let mut tgt_bounding_lt: Vec<LifetimeName> = Vec::new();

    let mut check_mut = true;
    let mut viable = false;
    let mut tgt_is_raw = false;

    let mut first = true;

    for tgt_lifetime in target_lifetimes.iter().rev() {
        // Get target bounding lifetime, which is the one "closest" to the value
        if first {
            if (tgt_lifetime.is_refcell) {
                continue;
            } else {
                tgt_bounding_lt = tgt_lifetime.names.clone();
                tgt_is_raw = tgt_lifetime.is_raw;
                first = false;
                continue;
            }
        }
        // Now check whether that borrow/pointer can actually be mutated
        // Note that this is not the same thing as whether the borrow/pointer is mutable
        // We're looking for cases like `&mut &T` or `&mut *const T` or `&mut *mut &T`
        if tgt_lifetime.is_refcell {
            // If we have a Refcell, then mutability is ensured.
            check_mut = false;
            continue;
        }
        if !check_mut {
            viable = true;
            break;
        }
        if check_mut && (!tgt_lifetime.is_mut) {
            viable = false;
            break;
        }
        viable = true;
    }
    if !viable {
        return (false, (Vec::new(), Vec::new()));
    }

    if (!src_is_raw) && (!tgt_is_raw) {
        return (false, (Vec::new(), Vec::new()));
    }
    if (src_is_raw && (!source_type.in_struct)) || (tgt_is_raw && (!target_type.in_struct)) {
        return (false, (Vec::new(), Vec::new()));
    }

    if tgt_bounding_lt.len() == 0 || tgt_bounding_lt.contains(&LifetimeName::Static) {
        return (true, (src_bounding_lt, tgt_bounding_lt));
    }

    for src_lt in src_bounding_lt.iter() {
        let mut flag = false;
        for tgt_lt in tgt_bounding_lt.iter() {
            if compare_lifetimes(src_lt, tgt_lt) {
                flag = true;
                break;
            } else {
                if lifetime_bounds
                    .iter() // Source should outlive the target
                    .any(|&(x, y)| compare_lifetimes(&x, &src_lt) && compare_lifetimes(&y, &tgt_lt))
                {
                    flag = true;
                    break;
                }
            }
        }
        // This source lifetime is not compatible with any of the target lifetimes
        if !flag {
            return (true, (Vec::from([*src_lt]), tgt_bounding_lt.clone()));
        }
    }
    (false, (Vec::new(), Vec::new()))
}
