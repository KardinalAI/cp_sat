use cp_sat::builder::CpModelBuilder;
use cp_sat::proto::CpSolverStatus;

#[test]
fn or() {
    let mut model = CpModelBuilder::default();
    let x = model.new_bool_var();
    let y = model.new_bool_var();
    model.add_or([x, y]);
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(x.solution_value(&response) || y.solution_value(&response));
}

#[test]
fn and() {
    let mut model = CpModelBuilder::default();
    let x = model.new_bool_var();
    let y = model.new_bool_var();
    model.add_and([x, y]);
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(x.solution_value(&response));
    assert!(y.solution_value(&response));
}

#[test]
fn at_most_one() {
    let mut model = CpModelBuilder::default();
    let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
    model.add_at_most_one(vars.iter().copied());
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(
        vars.iter()
            .map(|v| v.solution_value(&response) as u32)
            .sum::<u32>()
            <= 1
    );
}

#[test]
fn exactly_one() {
    let mut model = CpModelBuilder::default();
    let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
    model.add_exactly_one(vars.iter().copied());
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(
        vars.iter()
            .map(|v| v.solution_value(&response) as u32)
            .sum::<u32>()
            == 1
    );
}

#[test]
fn xor() {
    let mut model = CpModelBuilder::default();
    let vars: Vec<_> = (0..10).map(|_| model.new_bool_var()).collect();
    model.add_xor(vars.iter().copied());
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(
        vars.iter()
            .map(|v| v.solution_value(&response) as u32)
            .sum::<u32>()
            % 2
            == 1
    );
}

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
