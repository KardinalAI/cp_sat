use cp_sat::builder::CpModelBuilder;
use cp_sat::proto::CpSolverStatus;

#[test]
fn min() {
    let mut model = CpModelBuilder::default();
    let x = model.new_int_var([(0, 10)]);
    let y = model.new_int_var([(5, 15)]);
    let m = model.new_int_var([(-100, 100)]);
    model.add_min_eq(m, [x, y]);
    model.maximize(m);

    println!("{:#?}", model.proto());
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert_eq!(10., response.objective_value);
}

#[test]
fn max() {
    let mut model = CpModelBuilder::default();
    let x = model.new_int_var([(0, 10)]);
    let y = model.new_int_var([(5, 15)]);
    let m = model.new_int_var([(-100, 100)]);
    model.add_max_eq(m, [x, y]);
    model.minimize(m);

    println!("{:#?}", model.proto());
    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert_eq!(5., response.objective_value);
}
