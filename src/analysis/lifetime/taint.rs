use rustc_middle::mir::traversal;
use rustc_middle::mir::ProjectionElem::Field;
use rustc_middle::mir::{Body, Terminator, TerminatorKind};
use rustc_middle::mir::{Local, Operand, Place, Rvalue, Statement, StatementKind};

use crate::YugaConfig;

pub struct TaintAnalyzer<'a, 'b: 'a> {
    body: &'a Body<'b>,
    taint_list: Vec<(Local, Option<usize>)>,
    config: YugaConfig,
}

impl<'a, 'b: 'a> TaintAnalyzer<'a, 'b> {
    pub fn new(body: &'a Body<'b>, config: YugaConfig) -> Self {
        TaintAnalyzer {
            body,
            taint_list: Vec::new(),
            config,
        }
    }

    pub fn get_first_field_from_place(place: &Place) -> Option<usize> {
        let mut field_num: Option<usize> = None;

        for projection in place.projection.iter() {
            if let Field(field, ..) = projection {
                field_num = Some(field.index());
                break;
            }
        }
        return field_num;
    }

    fn update_taint(&mut self, rplace: &Place, lplace: &Place, debug: bool) {
        let lfield_num = Self::get_first_field_from_place(lplace);
        let rfield_num = Self::get_first_field_from_place(rplace);

        // If there an item in the taint list with field_num None, then it means that
        // a) there are no fields (primitive type), or
        // b) all the fields are tainted

        if rfield_num == None {
            // Exact match
            if self.taint_list.contains(&(rplace.local, None)) {
                if lfield_num == None {
                    // First remove all instances of the left side with field numbers
                    self.taint_list.retain(|&(a, b)| a != lplace.local);
                    // Then push the left local with None as the field,
                    // effectively tainting all its fields
                    self.taint_list.push((lplace.local, None));
                } else {
                    if !self.taint_list.contains(&(lplace.local, lfield_num)) {
                        self.taint_list.push((lplace.local, lfield_num));
                    }
                }
            }
            // Approx match (has the right local, but some not-None field)
            else if self.taint_list.iter().any(|&(a, b)| a == rplace.local) {
                if lfield_num == None {
                    // This case is straightforward. a.None <-- b.None,
                    // but only b.x is tainted.
                    // Then only a.x will be tainted
                    let tainted_rfields: Vec<Option<usize>> = self
                        .taint_list
                        .iter()
                        .filter(|&&(a, b)| a == rplace.local)
                        .map(|&(a, b)| b)
                        .collect();
                    for &b in tainted_rfields.iter() {
                        if !self.taint_list.contains(&(lplace.local, b)) {
                            self.taint_list.push((lplace.local, b));
                        }
                    }
                } else {
                    // Not so straightforward. a.x <-- b.None,
                    // but only b.y is in the taint list.
                    // We don't have sub-sub-fields, so a.x.y is not possible
                    // We choose to include.
                    if !self.taint_list.contains(&(lplace.local, lfield_num)) {
                        self.taint_list.push((lplace.local, lfield_num));
                    }
                }
            }
        } else {
            // If we have a.y <-- b.x

            if self.taint_list.contains(&(rplace.local, None))
                || self.taint_list.contains(&(rplace.local, rfield_num))
            {
                // If the taint list already contains a.None or a.y,
                // then no need to do anything.
                if !self.taint_list.contains(&(lplace.local, None))
                    && !self.taint_list.contains(&(lplace.local, lfield_num))
                {
                    self.taint_list.push((lplace.local, lfield_num));
                }
            }
        }
        if debug {
            println!(
                "{:?}.{:?} <-- {:?}.{:?}",
                lplace.local, lfield_num, rplace.local, rfield_num
            );
            println!("Taint list:\n{:?}", self.taint_list);
        }
    }

    pub fn mark_taint(&mut self, source_local: &Local, source_field: Option<usize>, debug: bool) {
        if debug {
            println!(
                "Checking for dataflow from {:?}.{:?}",
                source_local, source_field
            );
        }

        let mut edge_list: Vec<(Place, Place)> = Vec::new();

        // Reverse postorder is a natural linearization of control flow
        for (_, bb_data) in traversal::reverse_postorder(self.body) {
            for statement in &(bb_data.statements) {
                if let Statement {
                    kind: StatementKind::Assign(assign),
                    ..
                } = statement
                {
                    let mut lplace = &assign.0;
                    let rvalue = &assign.1;

                    let mut rplaces: Vec<Place> = Vec::new();

                    match (rvalue) {
                        Rvalue::Use(oper) | Rvalue::Repeat(oper, _) | Rvalue::Cast(_, oper, _) => {
                            match (oper) {
                                Operand::Move(pl) | Operand::Copy(pl) => {
                                    rplaces.push(*pl);
                                    if debug {
                                        print!("{:?} = {:?}\n", lplace, pl);
                                    }
                                }
                                _ => (),
                            }
                        }
                        Rvalue::Discriminant(pl)
                        | Rvalue::Ref(_, _, pl)
                        | Rvalue::CopyForDeref(pl) => {
                            rplaces.push(*pl);
                            if debug {
                                print!("{:?} = ref {:?}\n", lplace, pl);
                            }
                        }
                        Rvalue::BinaryOp(_, ops) => {
                            let (op1, op2) = &*(*ops);
                            match (op1) {
                                Operand::Move(pl) | Operand::Copy(pl) => {
                                    rplaces.push(*pl);
                                    if debug {
                                        print!("{:?} = {:?} op ", lplace, pl);
                                    }
                                }
                                _ => (),
                            }
                            match (op2) {
                                Operand::Move(pl) | Operand::Copy(pl) => {
                                    rplaces.push(*pl);
                                    if debug {
                                        print!("{:?}\n", pl);
                                    }
                                }
                                _ => (),
                            }
                        }
                        _ => (),
                    }

                    for rplace in &rplaces {
                        edge_list.push((*rplace, *lplace));
                        // edge_list.push((lplace, rplace));
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

                for arg in args {
                    match (arg.node) {
                        Operand::Move(rplace) | Operand::Copy(rplace) => {
                            edge_list.push((rplace, *lplace));
                            // edge_list.push((lplace, rplace));
                        }
                        _ => (),
                    }
                }

                // Potential dataflow between all pairs of input arguments to StaticCall
                for arg1 in args {
                    for arg2 in args {
                        if arg1 == arg2 {
                            continue;
                        }

                        match (arg1.node) {
                            Operand::Move(place1) | Operand::Copy(place1) => match (arg2.node) {
                                Operand::Move(place2) | Operand::Copy(place2) => {
                                    edge_list.push((place1, place2));
                                    edge_list.push((place2, place1));
                                }
                                _ => (),
                            },
                            _ => (),
                        }
                    }
                }
            }
        }

        self.taint_list.push((*source_local, source_field));

        let mut matched_source_field: bool = false;
        let mut matched_sink_field: bool = false;

        for (place1, place2) in edge_list.iter() {
            self.update_taint(place1, place2, debug);
        }
    }

    pub fn clear_taint(&mut self) {
        self.taint_list.clear();
    }

    pub fn check_taint(&self, sink_local: &Local, sink_field: Option<usize>) -> bool {
        if sink_field == None {
            if self.taint_list.iter().any(|&(a, _)| a == *sink_local) {
                return true;
            }
        } else {
            if self
                .taint_list
                .iter()
                .any(|&(a, b)| (a == *sink_local) && (b == sink_field || b == None))
            {
                return true;
            }
        }
        return false;
    }
}
