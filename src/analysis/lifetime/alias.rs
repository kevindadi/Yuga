use std::collections::{HashMap, HashSet};

use rustc_middle::mir::traversal;
use rustc_middle::mir::ProjectionElem::{Deref, Field};
use rustc_middle::mir::{Body, Terminator, TerminatorKind};
use rustc_middle::mir::{Local, Operand, Place, Rvalue, Statement, StatementKind};

use crate::analysis::lifetime::utils::FieldInfo;
use crate::analysis::lifetime::utils::MyProjection::{self, MyDeref, MyField};

use crate::YugaConfig;

pub struct AliasAnalyzer<'a, 'b: 'a> {
    body: &'a Body<'b>,
    points_to_map: HashMap<(Local, Option<usize>), HashSet<(Local, Option<usize>)>>,
    next_alloc: u32,
    config: YugaConfig,
}

impl<'a, 'b: 'a> AliasAnalyzer<'a, 'b> {
    pub fn new(body: &'a Body<'b>, config: YugaConfig) -> Self {
        AliasAnalyzer {
            body,
            points_to_map: HashMap::new(),
            next_alloc: Local::MAX_AS_U32,
            config,
        }
    }

    pub fn reset(&mut self) {
        self.points_to_map = HashMap::new();
        self.next_alloc = Local::MAX_AS_U32;
    }

    // Take a set of values and deref all of them
    fn apply_deref(
        &mut self,
        values: HashSet<(Local, Option<usize>)>,
        create_new: bool,
    ) -> HashSet<(Local, Option<usize>)> {
        let mut all_derefs: HashSet<(Local, Option<usize>)> = HashSet::new();

        for &(local, field) in values.iter() {
            match self.points_to_map.get(&(local, field)).cloned() {
                Some(deref_set) => {
                    all_derefs = all_derefs.union(&deref_set).map(|&k| k).collect();
                }
                None => {
                    // If it doesn't contain that field, but it contains the wildcard field
                    if field.is_some()
                        && self.points_to_map.contains_key(&(local, Some(usize::MAX)))
                    {
                        let deref_set = self
                            .points_to_map
                            .get(&(local, Some(usize::MAX)))
                            .unwrap()
                            .clone();
                        all_derefs = all_derefs.union(&deref_set).map(|&k| k).collect();
                        self.points_to_map.insert((local, field), deref_set);
                    }
                    if create_new {
                        self.points_to_map.insert(
                            (local, field),
                            HashSet::from([(Local::from_u32(self.next_alloc), None)]),
                        );
                        all_derefs.insert((Local::from_u32(self.next_alloc), None));
                        self.next_alloc -= 1;
                    }
                }
            }
        }
        all_derefs
    }

    // Take a set of values and apply a field access on all of them
    fn apply_field(
        &mut self,
        values: HashSet<(Local, Option<usize>)>,
        field: usize,
    ) -> HashSet<(Local, Option<usize>)> {
        let mut all_modified: HashSet<(Local, Option<usize>)> = HashSet::new();

        for &(l, f) in values.iter() {
            if f.is_some() {
                all_modified.insert((l, f));
            } else {
                all_modified.insert((l, Some(field)));

                if !self.points_to_map.contains_key(&(l, Some(field)))
                    && !self.points_to_map.contains_key(&(l, Some(usize::MAX)))
                {
                    self.points_to_map.insert(
                        (l, Some(field)),
                        HashSet::from([(Local::from_u32(self.next_alloc), None)]),
                    );
                    self.next_alloc -= 1;
                }
            }
        }
        all_modified
    }

    // There could be a field access, but we don't know which field. So try all options
    fn apply_unknown_field(
        &mut self,
        values: HashSet<(Local, Option<usize>)>,
    ) -> HashSet<(Local, Option<usize>)> {
        let mut all_modified: HashSet<(Local, Option<usize>)> = HashSet::new();

        for &(l, f) in values.iter() {
            if f.is_some() {
                all_modified.insert((l, f));
            } else {
                all_modified.insert((l, f));
                // All existing fields for that local
                let mut with_fields: HashSet<(Local, Option<usize>)> = self
                    .points_to_map
                    .keys()
                    .filter(|&&(a, b)| (a == l) && b.is_some())
                    .map(|&x| x)
                    .collect();
                if self.config.wildcard_field {
                    with_fields.insert((l, Some(usize::MAX))); // Wildcard field, matches anything
                }
                all_modified = all_modified.union(&with_fields).map(|&k| k).collect();
            }
        }
        all_modified
    }

    // L = R
    fn update_for_copy(
        &mut self,
        l_values: HashSet<(Local, Option<usize>)>,
        r_values: HashSet<(Local, Option<usize>)>,
    ) {
        for &(r_local, rfield_num) in r_values.iter() {
            for &(l_local, lfield_num) in l_values.iter() {
                if let Some(rpoints_set) = self.points_to_map.get(&(r_local, rfield_num)).cloned() {
                    match self.points_to_map.get_mut(&(l_local, lfield_num)) {
                        Some(lpoints_set) => {
                            let union_set: HashSet<(Local, Option<usize>)> =
                                lpoints_set.union(&rpoints_set).map(|&k| k).collect();
                            self.points_to_map.remove(&(l_local, lfield_num));
                            self.points_to_map.insert((l_local, lfield_num), union_set);
                            // self.points_to_map.insert((l_local, lfield_num), rpoints_set);
                        }
                        _ => {
                            self.points_to_map
                                .insert((l_local, lfield_num), rpoints_set);
                        }
                    }
                }
            }
            if rfield_num.is_none() {
                // If we have a.None = b.None, then connect all the respective fields of a and b.
                // Actually this can be a.x = b.None also, because our "field depth" is only 1
                let mut with_fields: HashSet<(Local, Option<usize>)> = self
                    .points_to_map
                    .keys()
                    .filter(|&&(a, b)| (a == r_local) && b.is_some())
                    .map(|&x| x)
                    .collect();
                for &(l, f) in with_fields.iter() {
                    if r_values.contains(&(l, f)) {
                        continue;
                    } // We've already covered this
                    let new_lvalues = self.apply_field(l_values.clone(), f.unwrap());
                    self.update_for_copy(new_lvalues, HashSet::from([(l, f)]));
                }
            }
        }
    }

    // L = &R
    fn update_for_ref(
        &mut self,
        l_values: HashSet<(Local, Option<usize>)>,
        r_values: HashSet<(Local, Option<usize>)>,
    ) {
        for &(l_local, lfield_num) in l_values.iter() {
            match self.points_to_map.get_mut(&(l_local, lfield_num)) {
                Some(lpoints_set) => {
                    let union_set: HashSet<(Local, Option<usize>)> =
                        lpoints_set.union(&r_values).map(|&k| k).collect();
                    self.points_to_map.remove(&(l_local, lfield_num));
                    self.points_to_map.insert((l_local, lfield_num), union_set);
                    // self.points_to_map.insert((l_local, lfield_num), r_values.clone());
                }
                _ => {
                    self.points_to_map
                        .insert((l_local, lfield_num), r_values.clone());
                }
            }
        }
    }

    // A place is a local and a series of projections (field or deref)
    // Start with the local and apply all these projections one by one
    fn decompose_place(&mut self, place: &Place) -> HashSet<(Local, Option<usize>)> {
        let mut values: HashSet<(Local, Option<usize>)> = HashSet::from([(place.local, None)]);

        for projection in place.projection.iter() {
            match projection {
                Deref => {
                    values = self.apply_deref(values, true);
                }
                Field(field, ..) => {
                    values = self.apply_field(values, field.index());
                }
                _ => (),
            }
        }
        values
    }

    // Keep applying deref and field access until you can't go further
    fn recursively_deref(&mut self, place: &Place) -> HashSet<(Local, Option<usize>)> {
        let mut values = self.decompose_place(place);

        let mut count = 0;

        loop {
            let old_values = values.clone();
            let derefs = self.apply_deref(values.clone(), false);
            let fields = self.apply_unknown_field(derefs.clone());
            values = values.union(&fields).map(|&k| k).collect();
            if values == old_values {
                break;
            }
            count += 1;
            if count > 1000 {
                panic!("Infinite loop in recursively_deref");
            }
        }
        values
    }

    pub fn check_alias(
        &mut self,
        source_local: &Local,
        source_proj: &Vec<MyProjection>,
        target_local: &Local,
        target_proj: &Vec<MyProjection>,
        debug: bool,
    ) -> bool {
        // The last thing MUST be a Deref
        // assert!((source_proj.len() > 0) && (*source_proj.last().unwrap() == MyDeref), "The last projection must be a Deref");
        // assert!((target_proj.len() > 0) && (*target_proj.last().unwrap() == MyDeref), "The last projection must be a Deref");

        if debug {
            println!("Source proj: {:?}", source_proj);
            println!("Target proj: {:?}", target_proj);
        }

        let mut source_values: HashSet<(Local, Option<usize>)> =
            HashSet::from([(*source_local, None)]);

        for proj in source_proj.iter() {
            match *proj {
                MyDeref => {
                    source_values = self.apply_deref(source_values, true);
                }
                MyField(FieldInfo { field_num, .. }) => {
                    source_values = self.apply_field(source_values, field_num);
                }
            }
        }

        if debug {
            println!("{:?}", self.points_to_map);
        }

        for (_, bb_data) in traversal::reverse_postorder(self.body) {
            for statement in &(bb_data.statements) {
                if let Statement {
                    kind: StatementKind::Assign(assign),
                    ..
                } = statement
                {
                    let mut lplace = &assign.0;
                    let rvalue = &assign.1;

                    let l_values = self.decompose_place(lplace);

                    if debug && lplace.local.index() == (0 as usize) {
                        println!("L-values: {:?}", l_values);
                    }

                    match (rvalue) {
                        Rvalue::Use(oper) | Rvalue::Repeat(oper, _) | Rvalue::Cast(_, oper, _) => {
                            match (oper) {
                                Operand::Move(rplace) | Operand::Copy(rplace) => {
                                    let r_values = self.decompose_place(rplace);
                                    self.update_for_copy(l_values.clone(), r_values);
                                }
                                _ => (),
                            }
                            if debug {
                                print!("{:?} = {:?}\n", lplace, oper);
                            }
                        }
                        Rvalue::CopyForDeref(rplace) => {
                            let r_values = self.decompose_place(rplace);
                            self.update_for_copy(l_values.clone(), r_values);
                            if debug {
                                print!("{:?} = {:?}\n", lplace, rplace);
                            }
                        }
                        Rvalue::Ref(_, _, rplace) => {
                            let r_values = self.decompose_place(rplace);
                            self.update_for_ref(l_values.clone(), r_values);
                            if debug {
                                print!("{:?} = ref {:?}\n", lplace, rplace);
                            }
                        }
                        Rvalue::BinaryOp(_, ops) => {
                            let (op1, op2) = &*(*ops);
                            match (op1) {
                                Operand::Move(rplace) | Operand::Copy(rplace) => {
                                    let r_values = self.decompose_place(rplace);
                                    self.update_for_copy(l_values.clone(), r_values);
                                    if debug {
                                        print!("{:?} = {:?} op ", lplace, rplace);
                                    }
                                }
                                _ => (),
                            }
                            match (op2) {
                                Operand::Move(rplace) | Operand::Copy(rplace) => {
                                    let r_values = self.decompose_place(rplace);
                                    self.update_for_copy(l_values.clone(), r_values);
                                    if debug {
                                        print!("{:?}\n", rplace);
                                    }
                                }
                                _ => (),
                            }
                        }
                        _ => (),
                    }
                    if debug {
                        println!("{:?}", self.points_to_map);
                    }
                }
            }

            if let Some(Terminator {
                kind:
                    TerminatorKind::Call {
                        args,
                        destination: lplace,
                        ..
                    },
                ..
            }) = &bb_data.terminator
            {
                if debug {
                    println!("{:?} = fn({:?})", lplace, args);
                }

                let mut l_values = self.decompose_place(lplace);
                l_values = self.apply_unknown_field(l_values);

                // Potential connection between all pairs of input arguments to StaticCall
                for arg1 in args {
                    for arg2 in args {
                        if arg1 == arg2 {
                            continue;
                        }

                        match (arg1.node) {
                            Operand::Move(place1) | Operand::Copy(place1) => {
                                match (arg2.node) {
                                    Operand::Move(place2) | Operand::Copy(place2) => {
                                        let values1 = self.recursively_deref(&place1);
                                        let values2 = self.recursively_deref(&place2);
                                        // A natural question is, what if value1 = &value2 inside the function?
                                        // Well that doesn't make sense, because value2 is owned by the function
                                        // and will be dropped when the function exits. Same for value2 = &value1
                                        self.update_for_copy(values1, values2);
                                    }
                                    _ => (),
                                }
                            }
                            _ => (),
                        }
                    }
                }
                // Once all the arguments have sorted themselves out,
                // connect them all back to the returned value
                for arg in args {
                    match (arg.node) {
                        Operand::Move(rplace) | Operand::Copy(rplace) => {
                            // let r_values = self.decompose_place(rplace);
                            let r_values = self.recursively_deref(&rplace);
                            self.update_for_copy(l_values.clone(), r_values);
                        }
                        _ => (),
                    }
                }
                if debug {
                    println!("{:?}", self.points_to_map);
                }
            }
        }
        let mut target_values: HashSet<(Local, Option<usize>)> =
            HashSet::from([(*target_local, None)]);

        for proj in target_proj.iter() {
            match *proj {
                MyDeref => {
                    target_values = self.apply_deref(target_values, false);
                }
                MyField(FieldInfo { field_num, .. }) => {
                    target_values = self.apply_field(target_values, field_num);
                }
            }
        }
        if debug {
            println!("Source values: {:?}", source_values);
            println!("Target values: {:?}", target_values);
        }
        source_values.iter().any(|x| target_values.contains(x))
    }
}
