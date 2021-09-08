use crate::proto;

#[derive(Default, Debug)]
pub struct CpModelBuilder {
    proto: proto::CpModelProto,
}

impl CpModelBuilder {
    pub fn proto(&self) -> &proto::CpModelProto {
        &self.proto
    }
    pub fn new_bool_var(&mut self) -> BoolVar {
        self.new_bool_var_with_name("")
    }
    pub fn new_bool_var_with_name(&mut self, name: impl Into<String>) -> BoolVar {
        let index = self.proto.variables.len() as i32;
        self.proto.variables.push(proto::IntegerVariableProto {
            name: name.into(),
            domain: vec![0, 1],
        });
        BoolVar(index)
    }
    pub fn new_int_var(&mut self, domain: impl IntoIterator<Item = (i64, i64)>) -> IntVar {
        self.new_int_var_with_name(domain, "")
    }
    pub fn new_int_var_with_name(
        &mut self,
        domain: impl IntoIterator<Item = (i64, i64)>,
        name: impl Into<String>,
    ) -> IntVar {
        let index = self.proto.variables.len() as i32;
        self.proto.variables.push(proto::IntegerVariableProto {
            name: name.into(),
            domain: domain.into_iter().flat_map(|(b, e)| [b, e]).collect(),
        });
        IntVar(index)
    }
    pub fn var_name(&self, var: impl Into<IntVar>) -> &str {
        &self.proto.variables[var.into().0 as usize].name
    }
    pub fn set_var_name(&mut self, var: impl Into<IntVar>, name: &str) {
        self.proto.variables[var.into().0 as usize].name = name.into();
    }

    pub fn add_or(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(proto::constraint_proto::Constraint::BoolOr(
                proto::BoolArgumentProto {
                    literals: vars.into_iter().map(|v| v.0).collect(),
                },
            )),
            ..Default::default()
        });
        Constraint(index)
    }
    pub fn add_and(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(proto::constraint_proto::Constraint::BoolAnd(
                proto::BoolArgumentProto {
                    literals: vars.into_iter().map(|v| v.0).collect(),
                },
            )),
            ..Default::default()
        });
        Constraint(index)
    }
    pub fn add_at_most_one(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(proto::constraint_proto::Constraint::AtMostOne(
                proto::BoolArgumentProto {
                    literals: vars.into_iter().map(|v| v.0).collect(),
                },
            )),
            ..Default::default()
        });
        Constraint(index)
    }
    pub fn add_exactly_one(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(proto::constraint_proto::Constraint::ExactlyOne(
                proto::BoolArgumentProto {
                    literals: vars.into_iter().map(|v| v.0).collect(),
                },
            )),
            ..Default::default()
        });
        Constraint(index)
    }
    pub fn add_xor(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(proto::constraint_proto::Constraint::BoolXor(
                proto::BoolArgumentProto {
                    literals: vars.into_iter().map(|v| v.0).collect(),
                },
            )),
            ..Default::default()
        });
        Constraint(index)
    }
    pub fn add_all_different(&mut self, vars: impl IntoIterator<Item = IntVar>) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(proto::constraint_proto::Constraint::AllDiff(
                proto::AllDifferentConstraintProto {
                    vars: vars.into_iter().map(|v| v.0).collect(),
                },
            )),
            ..Default::default()
        });
        Constraint(index)
    }

    pub fn stats(&self) -> String {
        crate::cp_model_stats(self.proto())
    }
    pub fn solve(&self) -> proto::CpSolverResponse {
        crate::solve(self.proto())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoolVar(i32);
impl BoolVar {
    pub fn solution_value(self, response: &proto::CpSolverResponse) -> bool {
        if self.0 < 0 {
            use std::ops::Not;
            !self.not().solution_value(response)
        } else {
            response.solution[self.0 as usize] != 0
        }
    }
}
impl std::ops::Not for BoolVar {
    type Output = Self;
    fn not(self) -> Self {
        Self(-self.0 - 1)
    }
}
impl std::fmt::Debug for BoolVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.0 < 0 {
            write!(f, "Not({:?})", !*self)
        } else {
            write!(f, "BoolVar({})", self.0)
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntVar(i32);
impl From<BoolVar> for IntVar {
    fn from(bool_var: BoolVar) -> IntVar {
        IntVar(bool_var.0)
    }
}
impl IntVar {
    pub fn solution_value(self, response: &proto::CpSolverResponse) -> i64 {
        if self.0 < 0 {
            use std::ops::Not;
            1 - IntVar::from(BoolVar(self.0).not()).solution_value(response)
        } else {
            response.solution[self.0 as usize]
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Constraint(usize);
