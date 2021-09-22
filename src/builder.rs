use crate::{ffi, proto};
use proto::constraint_proto::Constraint as CstEnum;
use smallvec::SmallVec;

/// A builder for CP SAT.
///
/// # Example
///
/// ```
/// # use cp_sat::builder::CpModelBuilder;
/// # use cp_sat::proto::CpSolverStatus;
/// let mut model = CpModelBuilder::default();
/// let x = model.new_bool_var();
/// let y = model.new_bool_var();
/// model.add_and([x, y]);
/// let response = model.solve();
/// assert_eq!(response.status(), CpSolverStatus::Optimal);
/// assert!(x.solution_value(&response));
/// assert!(y.solution_value(&response));
/// ```
#[derive(Default, Debug)]
pub struct CpModelBuilder {
    proto: proto::CpModelProto,
}

impl CpModelBuilder {
    /// Returns the corresponding [proto::CpModelProto].
    pub fn proto(&self) -> &proto::CpModelProto {
        &self.proto
    }

    /// Creates a new boolean variable, and returns the [BoolVar]
    /// indentifier.
    ///
    /// A boolean variable can be converted to an [IntVar] with the
    /// `std::convert::From` trait. In this case it acts as a variable
    /// within [0, 1].
    ///
    /// A [BoolVar] can be negated with [std::ops::Not], so you can
    /// use the `!` operator on it.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, IntVar};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// model.add_and([!x]);
    /// let _x_integer: IntVar = x.into();
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(!x.solution_value(&response));
    /// ```
    pub fn new_bool_var(&mut self) -> BoolVar {
        self.new_bool_var_with_name("")
    }

    /// Creates a new boolean variable with a name, and returns the
    /// [BoolVar] indentifier.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var_with_name("x");
    /// assert_eq!("x", model.var_name(x));
    /// ```
    pub fn new_bool_var_with_name(&mut self, name: impl Into<String>) -> BoolVar {
        let index = self.proto.variables.len() as i32;
        self.proto.variables.push(proto::IntegerVariableProto {
            name: name.into(),
            domain: vec![0, 1],
        });
        BoolVar(index)
    }
    /// Creates a new integer variable, and returns the [IntVar]
    /// indentifier.
    ///
    /// The domain of the variable is given. Bounds are included, so
    /// `[(0, 2), (4, 8)]` means [0, 2]∪[4, 8].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, IntVar};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 2), (4, 8)]);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// let x_val = x.solution_value(&response);
    /// assert!(0 <= x_val && x_val <= 2 || 4 <= x_val && 8 <= x_val);
    /// ```
    pub fn new_int_var(&mut self, domain: impl IntoIterator<Item = (i64, i64)>) -> IntVar {
        self.new_int_var_with_name(domain, "")
    }

    /// Creates a new integer variable with a name, and returns the
    /// [IntVar] indentifier.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var_with_name([(0, 10)], "x");
    /// assert_eq!("x", model.var_name(x));
    /// ```
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

    /// Returns the name of a variable, empty string if not setted.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var_with_name("x");
    /// assert_eq!("x", model.var_name(x));
    /// let y = model.new_int_var([(0, 2)]);
    /// assert_eq!("", model.var_name(y));
    /// ```
    pub fn var_name(&self, var: impl Into<IntVar>) -> &str {
        &self.proto.variables[var.into().0 as usize].name
    }

    /// Sets the variable name.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// model.set_var_name(x, "x");
    /// assert_eq!("x", model.var_name(x));
    /// ```
    pub fn set_var_name(&mut self, var: impl Into<IntVar>, name: &str) {
        self.proto.variables[var.into().0 as usize].name = name.into();
    }

    /// Returns the name of a constraint, empty string if not setted.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// let constraint = model.add_or([x]);
    /// assert_eq!("", model.constraint_name(constraint));
    /// model.set_constraint_name(constraint, "or");
    /// assert_eq!("or", model.constraint_name(constraint));
    /// ```
    pub fn constraint_name(&self, constraint: Constraint) -> &str {
        &self.proto.constraints[constraint.0].name
    }

    /// Sets the name of a constraint.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// let constraint = model.add_or([x]);
    /// model.set_constraint_name(constraint, "or");
    /// assert_eq!("or", model.constraint_name(constraint));
    /// ```
    pub fn set_constraint_name(&mut self, constraint: Constraint, name: &str) {
        self.proto.constraints[constraint.0].name = name.into();
    }

    /// Adds a boolean OR constraint on a list of [BoolVar].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// let y = model.new_bool_var();
    /// model.add_or([x, y]);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) || y.solution_value(&response));
    /// ```
    pub fn add_or(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::BoolOr(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }

    /// Adds a boolean AND constraint on a list of [BoolVar].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// let y = model.new_bool_var();
    /// model.add_and([x, y]);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response));
    /// assert!(y.solution_value(&response));
    /// ```
    pub fn add_and(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::BoolAnd(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }

    /// Adds a boolean "at most one" constraint on a list of [BoolVar].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
    /// model.add_at_most_one(vars.iter().copied());
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(
    ///     vars.iter()
    ///         .map(|v| v.solution_value(&response) as u32)
    ///         .sum::<u32>()
    ///         <= 1
    /// );
    /// ```
    pub fn add_at_most_one(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::AtMostOne(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }

    /// Adds a boolean "exactly one" constraint on a list of [BoolVar].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
    /// model.add_exactly_one(vars.iter().copied());
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(
    ///     vars.iter()
    ///         .map(|v| v.solution_value(&response) as u32)
    ///         .sum::<u32>()
    ///         == 1
    /// );
    /// ```
    pub fn add_exactly_one(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::ExactlyOne(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }

    /// Adds a boolean XOR constraint on a list of [BoolVar].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
    /// model.add_xor(vars.iter().copied());
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(
    ///     vars.iter()
    ///         .map(|v| v.solution_value(&response) as u32)
    ///         .sum::<u32>()
    ///         % 2
    ///         == 1
    /// );
    /// ```
    pub fn add_xor(&mut self, vars: impl IntoIterator<Item = BoolVar>) -> Constraint {
        self.add_cst(CstEnum::BoolXor(proto::BoolArgumentProto {
            literals: vars.into_iter().map(|v| v.0).collect(),
        }))
    }

    /// Adds a "all different" constraint on a list of [BoolVar].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 2)]);
    /// let y = model.new_int_var([(0, 2)]);
    /// let z = model.new_int_var([(0, 2)]);
    /// model.add_all_different([x, y, z]);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// let x_val = x.solution_value(&response);
    /// let y_val = y.solution_value(&response);
    /// let z_val = z.solution_value(&response);
    /// assert!(x_val != y_val);
    /// assert!(x_val != z_val);
    /// assert!(y_val != z_val);
    /// ```
    pub fn add_all_different(&mut self, vars: impl IntoIterator<Item = IntVar>) -> Constraint {
        self.add_cst(CstEnum::AllDiff(proto::AllDifferentConstraintProto {
            vars: vars.into_iter().map(|v| v.0).collect(),
        }))
    }

    /// Adds a linear constraint.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 100)]);
    /// let y = model.new_int_var([(0, 100)]);
    /// model.add_linear_constraint([(1, x), (3, y)], [(301, i64::MAX)]);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) + 3 * y.solution_value(&response) >= 301);
    /// ```
    pub fn add_linear_constraint(
        &mut self,
        expr: impl Into<LinearExpr>,
        domain: impl IntoIterator<Item = (i64, i64)>,
    ) -> Constraint {
        let expr = expr.into();
        let constant = expr.constant;
        self.add_cst(CstEnum::Linear(proto::LinearConstraintProto {
            vars: expr.vars.into_vec(),
            coeffs: expr.coeffs.into_vec(),
            domain: domain
                .into_iter()
                .flat_map(|(begin, end)| {
                    [
                        if begin == i64::MIN {
                            i64::MIN
                        } else {
                            begin.saturating_sub(constant)
                        },
                        if end == i64::MAX {
                            i64::MAX
                        } else {
                            end.saturating_sub(constant)
                        },
                    ]
                })
                .collect(),
        }))
    }

    /// Adds an equality constraint between 2 linear expressions.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 50)]);
    /// let y = model.new_int_var([(53, 100)]);
    /// model.add_eq(y, LinearExpr::from(x) + 3);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert_eq!(y.solution_value(&response), x.solution_value(&response) + 3);
    /// assert_eq!(50, x.solution_value(&response));
    /// assert_eq!(53, y.solution_value(&response));
    /// ```
    pub fn add_eq<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_linear_constraint(lhs.into() - rhs.into(), [(0, 0)])
    }

    /// Adds a greater or equal constraint between 2 linear expressions.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 50)]);
    /// let y = model.new_int_var([(50, 100)]);
    /// model.add_ge(x, y);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) >= y.solution_value(&response));
    /// assert_eq!(50, x.solution_value(&response));
    /// assert_eq!(50, y.solution_value(&response));
    /// ```
    pub fn add_ge<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_linear_constraint(lhs.into() - rhs.into(), [(0, i64::MAX)])
    }

    /// Adds a lesser or equal constraint between 2 linear expressions.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(50, 100)]);
    /// let y = model.new_int_var([(0, 50)]);
    /// model.add_le(x, y);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) <= y.solution_value(&response));
    /// assert_eq!(50, x.solution_value(&response));
    /// assert_eq!(50, y.solution_value(&response));
    /// ```
    pub fn add_le<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_linear_constraint(lhs.into() - rhs.into(), [(i64::MIN, 0)])
    }

    /// Adds a stricly greater constraint between 2 linear expressions.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 51)]);
    /// let y = model.new_int_var([(50, 100)]);
    /// model.add_gt(x, y);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) > y.solution_value(&response));
    /// assert_eq!(51, x.solution_value(&response));
    /// assert_eq!(50, y.solution_value(&response));
    /// ```
    pub fn add_gt<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_linear_constraint(lhs.into() - rhs.into(), [(1, i64::MAX)])
    }

    /// Adds a strictly lesser constraint between 2 linear expressions.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(50, 100)]);
    /// let y = model.new_int_var([(0, 51)]);
    /// model.add_lt(x, y);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) < y.solution_value(&response));
    /// assert_eq!(50, x.solution_value(&response));
    /// assert_eq!(51, y.solution_value(&response));
    /// ```
    pub fn add_lt<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_linear_constraint(lhs.into() - rhs.into(), [(i64::MIN, -1)])
    }

    /// Adds a not equal constraint between 2 linear expressions.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// model.add_ne(x, 1);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response) as i64 != 1);
    /// assert!(!x.solution_value(&response));
    /// ```
    pub fn add_ne<T: Into<LinearExpr>, U: Into<LinearExpr>>(
        &mut self,
        lhs: T,
        rhs: U,
    ) -> Constraint {
        self.add_linear_constraint(lhs.into() - rhs.into(), [(i64::MIN, -1), (1, i64::MAX)])
    }

    /// Adds a constraint that force the `target` to be equal to the
    /// minimum of the given `exprs`.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 10)]);
    /// let y = model.new_int_var([(5, 15)]);
    /// let m = model.new_int_var([(-100, 100)]);
    /// model.add_min_eq(m, [x, y]);
    /// model.maximize(m);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert_eq!(10., response.objective_value);
    /// assert_eq!(10, m.solution_value(&response));
    /// ```
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

    /// Adds a constraint that force the `target` to be equal to the
    /// maximum of the given `exprs`.
    ///
    /// # Exemple
    ///
    /// ```
    /// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 10)]);
    /// let y = model.new_int_var([(5, 15)]);
    /// let m = model.new_int_var([(-100, 100)]);
    /// model.add_max_eq(m, [x, y]);
    /// model.minimize(m);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert_eq!(5., response.objective_value);
    /// assert_eq!(5, m.solution_value(&response));
    /// ```
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

    /// Add a solution hint.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 100)]);
    /// let y = model.new_bool_var();
    /// model.add_hint(x, 42);
    /// model.add_hint(y, 1);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// ```
    pub fn add_hint(&mut self, var: impl Into<IntVar>, value: i64) {
        let var = var.into();
        let hints = self
            .proto
            .solution_hint
            .get_or_insert_with(Default::default);
        if var.0 < 0 {
            hints.vars.push(var.not().0);
            hints.values.push(1 - value);
        } else {
            hints.vars.push(var.0);
            hints.values.push(value);
        }
    }

    /// Delete all solution hints.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 100)]);
    /// let y = model.new_bool_var();
    /// model.add_hint(x, 42);
    /// model.add_hint(y, 1);
    /// model.del_hints();
    /// model.add_hint(x, 75);
    /// model.add_hint(y, 0);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// ```
    pub fn del_hints(&mut self) {
        self.proto.solution_hint = None;
    }

    /// Sets the minimization objective.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 100)]);
    /// model.minimize(x);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert_eq!(0, x.solution_value(&response));
    /// assert_eq!(0., response.objective_value);
    /// ```
    pub fn minimize<T: Into<LinearExpr>>(&mut self, expr: T) {
        let expr = expr.into();
        self.proto.objective = Some(proto::CpObjectiveProto {
            vars: expr.vars.into_vec(),
            coeffs: expr.coeffs.into_vec(),
            offset: expr.constant as f64,
            scaling_factor: 1.,
            domain: vec![],
        });
    }

    /// Sets the maximization objective.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 100)]);
    /// model.maximize(x);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert_eq!(100, x.solution_value(&response));
    /// assert_eq!(100., response.objective_value);
    /// ```
    pub fn maximize<T: Into<LinearExpr>>(&mut self, expr: T) {
        let mut expr = expr.into();
        for coeff in &mut expr.coeffs {
            *coeff *= -1;
        }
        self.proto.objective = Some(proto::CpObjectiveProto {
            vars: expr.vars.into_vec(),
            coeffs: expr.coeffs.into_vec(),
            offset: -expr.constant as f64,
            scaling_factor: -1.,
            domain: vec![],
        });
    }

    /// Returns some statistics on the model.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// let model = CpModelBuilder::default();
    /// let stats = model.stats();
    /// assert!(!stats.is_empty());
    /// ```
    pub fn stats(&self) -> String {
        ffi::cp_model_stats(self.proto())
    }

    /// Verifies that the given model satisfies all the properties
    /// described in the proto comments. Returns an empty string if it is
    /// the case, otherwise fails at the first error and returns a
    /// human-readable description of the issue.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, -1)]);
    /// model.maximize(x);
    /// assert!(!model.validate_cp_model().is_empty());
    /// ```
    pub fn validate_cp_model(&self) -> String {
        ffi::validate_cp_model(self.proto())
    }

    /// Solves the model, and returns the corresponding [proto::CpSolverResponse].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::CpSolverStatus;
    /// let model = CpModelBuilder::default();
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// ```
    pub fn solve(&self) -> proto::CpSolverResponse {
        ffi::solve(self.proto())
    }

    /// Solves the model with the given
    /// [parameters][proto::SatParameters], and returns the
    /// corresponding [proto::CpSolverResponse].
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::{CpSolverStatus, SatParameters};
    /// let model = CpModelBuilder::default();
    /// let mut params = SatParameters::default();
    /// params.max_deterministic_time = Some(1.);
    /// let response = model.solve_with_parameters(&params);
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// ```
    pub fn solve_with_parameters(&self, params: &proto::SatParameters) -> proto::CpSolverResponse {
        ffi::solve_with_parameters(self.proto(), params)
    }
}

/// Boolean variable identifier.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoolVar(i32);
impl BoolVar {
    /// Gets the solution value of the variable from a solution.
    ///
    /// The solution must come from the same model as the variable,
    /// and a solution must be present in the response.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::{CpSolverStatus, SatParameters};
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_bool_var();
    /// model.add_or([x]);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert!(x.solution_value(&response));
    /// ```
    #[track_caller]
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

/// Integer variable identifier.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntVar(i32);
impl From<BoolVar> for IntVar {
    fn from(bool_var: BoolVar) -> IntVar {
        IntVar(bool_var.0)
    }
}
impl IntVar {
    /// Gets the solution value of the variable from a solution.
    ///
    /// The solution must come from the same model as the variable,
    /// and a solution must be present in the response.
    ///
    /// # Example
    ///
    /// ```
    /// # use cp_sat::builder::CpModelBuilder;
    /// # use cp_sat::proto::{CpSolverStatus, SatParameters};
    /// let mut model = CpModelBuilder::default();
    /// let x = model.new_int_var([(0, 42)]);
    /// model.maximize(x);
    /// let response = model.solve();
    /// assert_eq!(response.status(), CpSolverStatus::Optimal);
    /// assert_eq!(42, x.solution_value(&response));
    /// ```
    #[track_caller]
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

/// Constraint identifier.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Constraint(usize);

/// A linear expression, used in several places in the
/// [builder][CpModelBuilder].
///
/// It describes an expression in the form `ax+by+c`. Several [From]
/// and [std::ops] traits are implemented for easy modeling.
///
/// # Exemple
///
/// Most of the builder methods that takes something linear take in
/// practice a `impl Into<LinearExpr>`.  In the example, we will use
/// [CpModelBuilder::maximize].
///
/// ```
/// # use cp_sat::builder::{CpModelBuilder, LinearExpr};
/// let mut model = CpModelBuilder::default();
/// let x1 = model.new_int_var([(0, 100)]);
/// let x2 = model.new_int_var([(0, 100)]);
/// let y1 = model.new_bool_var();
/// let y2 = model.new_bool_var();
/// model.maximize(x1); // IntVar can be converted in LinearExpr
/// model.maximize(y1); // as BoolVar
/// model.maximize(42); // as i64
/// model.maximize((42, x1)); // this means maximize 42 * x1
/// model.maximize((42, y1)); // works also with BoolVar
/// model.maximize([(42, x1), (1337, x2)]); // with array: 42*x1 + 1337*x2
/// model.maximize([(42, y1), (1337, y2)]); // with array: also with bool
/// model.maximize([(42, x1), (1337, y2.into())]); // BoolVar conversion
///
/// // for easy looping, we can also modify a LinearExpr
/// let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
/// let mut expr = LinearExpr::default(); // means 0, can also be LinearExpr::from(0)
/// for (i, v) in vars.iter().copied().enumerate() {
///     match i {
///         0..=1 => expr += (i as i64, v),
///         2..=3 => expr -= (42, v),
///         4..=5 => expr += v,
///         _ => expr -= LinearExpr::from([(42, v), (1337, y1)]) + 5,
///     }
/// }
///
/// // an iterator of `Into<LinearExpr>` can be collected or extended,
/// // meaning summing the elements
/// model.maximize(vars.iter().copied().collect::<LinearExpr>()); // means sum(vars)
/// expr.extend(vars.iter().map(|&v| (2, v))); // means expr += sum_vars(2 * v)
/// ```
#[derive(Clone, Default, Debug)]
pub struct LinearExpr {
    vars: SmallVec<[i32; 4]>,
    coeffs: SmallVec<[i64; 2]>,
    constant: i64,
}

impl<E: Into<LinearExpr>> std::ops::AddAssign<E> for LinearExpr {
    fn add_assign(&mut self, rhs: E) {
        let mut rhs = rhs.into();
        if self.vars.len() < rhs.vars.len() {
            std::mem::swap(self, &mut rhs);
        }
        self.vars.extend_from_slice(&rhs.vars);
        self.coeffs.extend_from_slice(&rhs.coeffs);
        self.constant += rhs.constant;
    }
}
impl std::ops::Neg for LinearExpr {
    type Output = LinearExpr;
    fn neg(mut self) -> Self::Output {
        for c in &mut self.coeffs {
            *c = -*c;
        }
        self.constant = -self.constant;
        self
    }
}
impl<L: Into<LinearExpr>> std::ops::SubAssign<L> for LinearExpr {
    fn sub_assign(&mut self, rhs: L) {
        *self += -rhs.into();
    }
}

impl<V: Into<IntVar>> From<V> for LinearExpr {
    fn from(var: V) -> Self {
        Self::from((1, var))
    }
}
impl From<i64> for LinearExpr {
    fn from(constant: i64) -> Self {
        let mut res = Self::default();
        res.constant += constant;
        res
    }
}
impl<V: Into<IntVar>> From<(i64, V)> for LinearExpr {
    fn from((coeff, var): (i64, V)) -> Self {
        let mut res = Self::default();
        let var = var.into();
        if var.0 < 0 {
            res.vars.push(var.not().0);
            res.coeffs.push(-coeff);
            res.constant += coeff;
        } else {
            res.vars.push(var.0);
            res.coeffs.push(coeff);
        }
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

impl<T: Into<LinearExpr>> std::ops::Add<T> for LinearExpr {
    type Output = LinearExpr;
    fn add(mut self, rhs: T) -> Self::Output {
        self += rhs.into();
        self
    }
}

impl<T: Into<LinearExpr>> std::ops::Sub<T> for LinearExpr {
    type Output = LinearExpr;
    fn sub(mut self, rhs: T) -> Self::Output {
        self -= rhs.into();
        self
    }
}

impl From<LinearExpr> for proto::LinearExpressionProto {
    fn from(expr: LinearExpr) -> Self {
        proto::LinearExpressionProto {
            vars: expr.vars.into_vec(),
            coeffs: expr.coeffs.into_vec(),
            offset: expr.constant,
        }
    }
}

impl<T: Into<LinearExpr>> std::iter::Extend<T> for LinearExpr {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for e in iter {
            *self += e;
        }
    }
}
impl<T: Into<LinearExpr>> std::iter::FromIterator<T> for LinearExpr {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut res = LinearExpr::default();
        res.extend(iter);
        res
    }
}
