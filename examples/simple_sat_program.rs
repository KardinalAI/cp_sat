fn main() {
    let mut model = cp_sat::builder::CpModelBuilder::default();
    let x = model.new_int_var_with_name([(0, 2)], "x");
    let y = model.new_int_var_with_name([(0, 2)], "y");
    let z = model.new_int_var_with_name([(0, 2)], "z");
    model.add_all_different([x, y, z]);
    println!("{:#?}", model);
    println!("model stats: {}", model.stats());
    let response = model.solve();
    println!("{:#?}", response);
    println!(
        "response stats: {}",
        cp_sat::cp_solver_response_stats(&response, false)
    );
    assert_eq!(response.status(), cp_sat::proto::CpSolverStatus::Optimal);
    assert!(x.solution_value(&response) != y.solution_value(&response));
    assert!(x.solution_value(&response) != z.solution_value(&response));
    assert!(y.solution_value(&response) != z.solution_value(&response));
}
