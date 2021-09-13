use cp_sat::builder::CpModelBuilder;
use cp_sat::proto::CpSolverStatus;

#[test]
fn not_infeasible() {
    let mut model = CpModelBuilder::default();
    let x = model.new_bool_var();
    model.add_and([x, !x]);
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Infeasible);
}

#[test]
fn not_feasible() {
    let mut model = CpModelBuilder::default();
    let x = model.new_bool_var();
    let y = model.new_bool_var();
    model.add_and([x, !y]);
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(x.solution_value(&response));
    assert!(!(!x).solution_value(&response));
    assert!(!y.solution_value(&response));
    assert!((!y).solution_value(&response));
}
