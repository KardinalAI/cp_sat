use cp_sat::builder::CpModelBuilder;
use cp_sat::proto::{CpSolverStatus, SatParameters};

#[test]
fn presentation_problem() {
    let mut model = CpModelBuilder::default();
    let domain = [(0, 2)];
    let x = model.new_int_var_with_name(domain, "x");
    let y = model.new_int_var_with_name(domain, "y");
    let z = model.new_int_var_with_name(domain, "z");

    model.add_ne(x, y);

    let response = model.solve();
    println!("{:?}", response);

    assert_eq!(response.status(), CpSolverStatus::Optimal);
    let x_val = x.solution_value(&response);
    let y_val = y.solution_value(&response);
    let z_val = z.solution_value(&response);
    println!("x = {}", x_val);
    println!("y = {}", y_val);
    println!("z = {}", z_val);

    assert!(x_val != y_val);
    assert!(0 <= x_val && x_val <= 2);
    assert!(0 <= y_val && y_val <= 2);
    assert!(0 <= z_val && z_val <= 2);
}

#[test]
fn solving_a_cp_problem() {
    let mut model = CpModelBuilder::default();
    let var_upper_bound = vec![50, 45, 37].into_iter().max().unwrap();
    let x = model.new_int_var_with_name([(0, var_upper_bound)], "x");
    let y = model.new_int_var_with_name([(0, var_upper_bound)], "y");
    let z = model.new_int_var_with_name([(0, var_upper_bound)], "z");

    model.add_le([(2, x), (7, y), (3, z)], 50);
    model.add_le([(3, x), (-5, y), (7, z)], 45);
    model.add_le([(5, x), (2, y), (-6, z)], 37);

    model.maximize([(2, x), (2, y), (3, z)]);

    let response = model.solve();
    assert_eq!(response.status(), CpSolverStatus::Optimal);
    let x_val = x.solution_value(&response);
    let y_val = y.solution_value(&response);
    let z_val = z.solution_value(&response);
    println!("objective: {}", response.objective_value);
    println!("x = {}", x_val);
    println!("y = {}", y_val);
    println!("z = {}", z_val);

    assert_eq!(35., response.objective_value);
    assert!(2 * x_val + 7 * y_val + 3 * z_val <= 50);
    assert!(3 * x_val - 5 * y_val + 7 * z_val <= 45);
    assert!(5 * x_val + 2 * y_val - 6 * z_val <= 37);
}

#[test]
fn solve_with_time_limit_sample_sat() {
    let mut model = CpModelBuilder::default();
    let domain = [(0, 2)];
    let x = model.new_int_var_with_name(domain, "x");
    let y = model.new_int_var_with_name(domain, "y");
    let z = model.new_int_var_with_name(domain, "z");

    model.add_ne(x, y);

    let mut params = SatParameters::default();
    params.max_time_in_seconds = Some(10.);

    let response = model.solve_with_parameters(&params);
    println!("{:?}", response);

    assert_eq!(response.status(), CpSolverStatus::Optimal);
    let x_val = x.solution_value(&response);
    let y_val = y.solution_value(&response);
    let z_val = z.solution_value(&response);
    println!("x = {}", x_val);
    println!("y = {}", y_val);
    println!("z = {}", z_val);
}
