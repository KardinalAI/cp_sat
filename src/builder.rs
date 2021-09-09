use crate::proto;
use proto::constraint_proto::Constraint as CstEnum;

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
        self.add_cst(CstEnum::BoolOr(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }
    pub fn add_and(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::BoolAnd(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }
    pub fn add_at_most_one(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::AtMostOne(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }
    pub fn add_exactly_one(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::ExactlyOne(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }
    pub fn add_xor(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::BoolXor(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }
    pub fn add_all_different(&mut self, vars: impl IntoIterator<Item = IntVar>) -> Constraint {
        self.add_cst(CstEnum::AllDiff(proto::AllDifferentConstraintProto {
            vars: vars.into_iter().map(|v| v.0).collect(),
        }))
    }
    pub fn add_linear_constraint(
        &mut self,
        expr: &LinearExpr,
        (begin, end): (i64, i64),
    ) -> Constraint {
        self.add_cst(CstEnum::Linear(proto::LinearConstraintProto {
            vars: expr.vars.clone(),
            coeffs: expr.coeffs.clone(),
            domain: vec![begin - expr.constant, end - expr.constant],
        }))
    }
    pub fn add_eq<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_eq_by_ref(&lhs.into(), &rhs.into())
    }
    pub fn add_eq_by_ref(&mut self, lhs: &LinearExpr, rhs: &LinearExpr) -> Constraint {
        let (mut cst, val) = create_linear_cst_proto(lhs, rhs);
        cst.domain.extend([val, val]);
        self.add_cst(CstEnum::Linear(cst))
    }
    pub fn add_ge<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_ge_by_ref(&lhs.into(), &rhs.into())
    }
    pub fn add_ge_by_ref(&mut self, lhs: &LinearExpr, rhs: &LinearExpr) -> Constraint {
        let (mut cst, val) = create_linear_cst_proto(lhs, rhs);
        cst.domain.extend([val, i64::MAX]);
        self.add_cst(CstEnum::Linear(cst))
    }
    pub fn add_le<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_le_by_ref(&lhs.into(), &rhs.into())
    }
    pub fn add_le_by_ref(&mut self, lhs: &LinearExpr, rhs: &LinearExpr) -> Constraint {
        let (mut cst, val) = create_linear_cst_proto(lhs, rhs);
        cst.domain.extend([i64::MIN, val]);
        self.add_cst(CstEnum::Linear(cst))
    }
    pub fn add_gt<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_gt_by_ref(&lhs.into(), &rhs.into())
    }
    pub fn add_gt_by_ref(&mut self, lhs: &LinearExpr, rhs: &LinearExpr) -> Constraint {
        let (mut cst, val) = create_linear_cst_proto(lhs, rhs);
        cst.domain.extend([val + 1, i64::MAX]);
        self.add_cst(CstEnum::Linear(cst))
    }
    pub fn add_lt<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_lt_by_ref(&lhs.into(), &rhs.into())
    }
    pub fn add_lt_by_ref(&mut self, lhs: &LinearExpr, rhs: &LinearExpr) -> Constraint {
        let (mut cst, val) = create_linear_cst_proto(lhs, rhs);
        cst.domain.extend([i64::MIN, val - 1]);
        self.add_cst(CstEnum::Linear(cst))
    }
    pub fn add_ne<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_ne_by_ref(&lhs.into(), &rhs.into())
    }
    pub fn add_ne_by_ref(&mut self, lhs: &LinearExpr, rhs: &LinearExpr) -> Constraint {
        let (mut cst, val) = create_linear_cst_proto(lhs, rhs);
        cst.domain.extend([i64::MIN, val - 1, val + 1, i64::MAX]);
        self.add_cst(CstEnum::Linear(cst))
    }
    pub fn add_min_eq(
        &mut self,
        target: impl Into<LinearExpr>,
        exprs: impl IntoIterator<Item = impl Into<LinearExpr>>,
    ) -> Constraint {
        self.add_cst(CstEnum::LinMin(proto::LinearArgumentProto {
            target: Some(target.into().into()),
            exprs: exprs.into_iter().map(|e| e.into().into()).collect(),
        }))
    }
    pub fn add_max_eq(
        &mut self,
        target: impl Into<LinearExpr>,
        exprs: impl IntoIterator<Item = impl Into<LinearExpr>>,
    ) -> Constraint {
        self.add_cst(CstEnum::LinMax(proto::LinearArgumentProto {
            target: Some(target.into().into()),
            exprs: exprs.into_iter().map(|e| e.into().into()).collect(),
        }))
    }
    fn add_cst(&mut self, cst: CstEnum) -> Constraint {
        let index = self.proto.constraints.len();
        self.proto.constraints.push(proto::ConstraintProto {
            constraint: Some(cst),
            ..Default::default()
        });
        Constraint(index)
    }

    pub fn minimize<T: Into<LinearExpr>>(&mut self, expr: T) {
        let expr = expr.into();
        self.proto.objective = Some(proto::CpObjectiveProto {
            vars: expr.vars,
            coeffs: expr.coeffs,
            offset: expr.constant as f64,
            scaling_factor: 1.,
            domain: vec![],
        });
    }
    pub fn maximize<T: Into<LinearExpr>>(&mut self, expr: T) {
        let mut expr = expr.into();
        for coeff in &mut expr.coeffs {
            *coeff *= -1;
        }
        self.proto.objective = Some(proto::CpObjectiveProto {
            vars: expr.vars,
            coeffs: expr.coeffs,
            offset: -expr.constant as f64,
            scaling_factor: -1.,
            domain: vec![],
        });
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
            1 - self.not().solution_value(response)
        } else {
            response.solution[self.0 as usize]
        }
    }
    fn not(self) -> Self {
        IntVar::from(!BoolVar(self.0))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Constraint(usize);

#[derive(Clone, Default, Debug)]
pub struct LinearExpr {
    vars: Vec<i32>,
    coeffs: Vec<i64>,
    constant: i64,
}
impl std::ops::AddAssign<i64> for LinearExpr {
    fn add_assign(&mut self, rhs: i64) {
        self.constant += rhs;
    }
}
impl<V: Into<IntVar>> std::ops::AddAssign<(i64, V)> for LinearExpr {
    fn add_assign(&mut self, (coeff, var): (i64, V)) {
        let var = var.into();
        if var.0 < 0 {
            self.vars.push(var.not().0);
            self.coeffs.push(-coeff);
            self.constant += coeff;
        } else {
            self.vars.push(var.0);
            self.coeffs.push(coeff);
        }
    }
}
impl<V: Into<IntVar>> std::ops::AddAssign<V> for LinearExpr {
    fn add_assign(&mut self, var: V) {
        *self += (1, var);
    }
}
impl<V: Into<IntVar>> std::iter::Extend<(i64, V)> for LinearExpr {
    fn extend<I: IntoIterator<Item = (i64, V)>>(&mut self, iter: I) {
        for (coeff, var) in iter.into_iter() {
            *self += (coeff, var.into());
        }
    }
}
impl<V: Into<IntVar>> std::iter::FromIterator<(i64, V)> for LinearExpr {
    fn from_iter<I: IntoIterator<Item = (i64, V)>>(iter: I) -> Self {
        let mut res = Self::default();
        res.extend(iter);
        res
    }
}
impl<V: Into<IntVar>> std::iter::Extend<V> for LinearExpr {
    fn extend<I: IntoIterator<Item = V>>(&mut self, iter: I) {
        for var in iter.into_iter() {
            *self += var.into();
        }
    }
}
impl<V: Into<IntVar>> std::iter::FromIterator<V> for LinearExpr {
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let mut res = Self::default();
        res.extend(iter);
        res
    }
}
impl<V: Into<IntVar>> From<V> for LinearExpr {
    fn from(var: V) -> Self {
        let mut res = Self::default();
        res += var;
        res
    }
}
impl From<i64> for LinearExpr {
    fn from(constant: i64) -> Self {
        let mut res = Self::default();
        res += constant;
        res
    }
}
impl<V: Into<IntVar>, const L: usize> From<[(i64, V); L]> for LinearExpr {
    fn from(expr: [(i64, V); L]) -> Self {
        let mut res = Self::default();
        for term in expr {
            res += term;
        }
        res
    }
}
impl<T> std::ops::Add<T> for LinearExpr
where
    LinearExpr: std::ops::AddAssign<T>,
{
    type Output = LinearExpr;
    fn add(mut self, rhs: T) -> Self::Output {
        self += rhs;
        self
    }
}
impl From<LinearExpr> for proto::LinearExpressionProto {
    fn from(expr: LinearExpr) -> Self {
        proto::LinearExpressionProto {
            vars: expr.vars,
            coeffs: expr.coeffs,
            offset: expr.constant,
        }
    }
}

fn create_linear_cst_proto(
    left: &LinearExpr,
    right: &LinearExpr,
) -> (proto::LinearConstraintProto, i64) {
    (
        proto::LinearConstraintProto {
            vars: left
                .vars
                .iter()
                .copied()
                .chain(right.vars.iter().copied())
                .collect(),
            coeffs: left
                .coeffs
                .iter()
                .copied()
                .chain(right.coeffs.iter().map(|&c| -c))
                .collect(),
            domain: vec![],
        },
        right.constant - left.constant,
    )
}
