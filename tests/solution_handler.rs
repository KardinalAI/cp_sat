use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;
use cp_sat::builder::CpModelBuilder;
use cp_sat::proto::{SatParameters, CpSolverResponse};

/// In a non-optimization problem all feasible solutions should be found.
#[test]
fn enumeration_solution_handler() {
  let mut model = CpModelBuilder::default();
  // linear constraint will only allow a = 2, a = 3 and a = 4
  let a = model.new_int_var([(2, 7)]);
  model.add_linear_constraint([(3, a)], [(0, 13)]);
  let mut params = SatParameters::default();
  params.enumerate_all_solutions = Some(true);

  let memory = Rc::new(RefCell::new(Vec::new()));
  let memory2 = memory.clone();
  let handler = move |response: CpSolverResponse| {
    memory2.borrow_mut().push(response);
  };

  let _response = model.solve_with_parameters_and_handler(&params, handler);

  assert_eq!(3, memory.borrow().len());

  let expected = HashSet::from([2, 3, 4]);
  let actual = memory
      .borrow()
      .iter()
      .map(|response| a.solution_value(response))
      .collect::<HashSet::<i64>>();

  assert_eq!(expected, actual);
}

/// In an optimization problem at least one feasible solution should be found.
#[test]
fn optimization_solution_handler() {
   let mut model = CpModelBuilder::default();
  // linear constraint will only allow a = 2, a = 3 and a = 4
  let a = model.new_int_var([(2, 7)]);
  model.add_linear_constraint([(3, a)], [(0, 13)]);
  model.minimize(a);
  let mut params = SatParameters::default();
  params.enumerate_all_solutions = Some(true);

  let memory = Rc::new(RefCell::new(Vec::new()));
  let memory2 = memory.clone();
  let handler = move |response: CpSolverResponse| {
    memory2.borrow_mut().push(response);
  };

  let response = model.solve_with_parameters_and_handler(&params, handler);

  assert_eq!(2, a.solution_value(&response));

  // At least one feasible solution is encountered.
  // As we do not know how often the solution improves, or whether the first
  // feasible solution is already the optimal one, we cannot expect more than one
  // improvement.
  assert!(memory.borrow().len() >= 1);
}
