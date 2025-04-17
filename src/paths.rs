use std::collections::HashSet;

use rustc_span::Symbol;

/*
How to find a path for unknown item:
1. Modify tests/utility/rurda_paths_discovery.rs
2. cargo run --bin yuga -- --crate-type lib tests/utility/yuga_paths_discovery.rs

For temporary debugging, you can also change this line in `prelude.rs`
`let names = self.get_def_path(def_id);`
to
`let names = dbg!(self.get_def_path(def_id));`
*/
// Strong bypasses
pub const PTR_READ: [&str; 3] = ["core", "ptr", "read"];
pub const PTR_DIRECT_READ: [&str; 5] = ["core", "ptr", "const_ptr", "<impl *const T>", "read"];

pub const INTRINSICS_COPY: [&str; 3] = ["core", "intrinsics", "copy"];
pub const INTRINSICS_COPY_NONOVERLAPPING: [&str; 3] = ["core", "intrinsics", "copy_nonoverlapping"];

pub const VEC_SET_LEN: [&str; 4] = ["alloc", "vec", "Vec", "set_len"];
pub const VEC_FROM_RAW_PARTS: [&str; 4] = ["alloc", "vec", "Vec", "from_raw_parts"];

// Weak bypasses
pub const TRANSMUTE: [&str; 4] = ["core", "intrinsics", "", "transmute"];

pub const PTR_WRITE: [&str; 3] = ["core", "ptr", "write"];
pub const PTR_DIRECT_WRITE: [&str; 5] = ["core", "ptr", "mut_ptr", "<impl *mut T>", "write"];

pub const PTR_AS_REF: [&str; 5] = ["core", "ptr", "const_ptr", "<impl *const T>", "as_ref"];
pub const PTR_AS_MUT: [&str; 5] = ["core", "ptr", "mut_ptr", "<impl *mut T>", "as_mut"];
pub const NON_NULL_AS_REF: [&str; 5] = ["core", "ptr", "non_nul", "NonNull", "as_ref"];
pub const NON_NULL_AS_MUT: [&str; 5] = ["core", "ptr", "non_nul", "NonNull", "as_mut"];

pub const SLICE_GET_UNCHECKED: [&str; 4] = ["core", "slice", "<impl [T]>", "get_unchecked"];
pub const SLICE_GET_UNCHECKED_MUT: [&str; 4] = ["core", "slice", "<impl [T]>", "get_unchecked_mut"];

pub const PTR_SLICE_FROM_RAW_PARTS: [&str; 3] = ["core", "ptr", "slice_from_raw_parts"];
pub const PTR_SLICE_FROM_RAW_PARTS_MUT: [&str; 3] = ["core", "ptr", "slice_from_raw_parts_mut"];
pub const SLICE_FROM_RAW_PARTS: [&str; 3] = ["core", "slice", "from_raw_parts"];
pub const SLICE_FROM_RAW_PARTS_MUT: [&str; 3] = ["core", "slice", "from_raw_parts_mut"];

// Generic function call
pub const PTR_DROP_IN_PLACE: [&str; 3] = ["core", "ptr", "drop_in_place"];
pub const PTR_DIRECT_DROP_IN_PLACE: [&str; 5] =
    ["core", "ptr", "mut_ptr", "<impl *mut T>", "drop_in_place"];

pub struct PathSet {
    set: HashSet<Vec<Symbol>>,
}

impl PathSet {
    pub fn new(path_arr: &[&[&str]]) -> Self {
        let mut set = HashSet::new();
        for path in path_arr {
            let path_vec = path.iter().map(|p| Symbol::intern(p)).collect::<Vec<_>>();
            set.insert(path_vec);
        }

        PathSet { set }
    }

    pub fn contains(&self, target: &Vec<Symbol>) -> bool {
        self.set.contains(target)
    }
}
