use cp_sat::builder::CpModelBuilder;
use cp_sat::proto::CpSolverStatus;

fn main() {
    let mut model = CpModelBuilder::default();

    let x = model.new_int_var_with_name([(0, 2)], "x");
    let y = model.new_int_var_with_name([(0, 2)], "y");
    let z = model.new_int_var_with_name([(0, 2)], "z");

    model.add_ne(x, y);

    let response = model.solve();
    println!(
        "{}",
        cp_sat::ffi::cp_solver_response_stats(&response, false)
    );

    if response.status() == CpSolverStatus::Optimal {
        println!("x = {}", x.solution_value(&response));
        println!("y = {}", y.solution_value(&response));
        println!("z = {}", z.solution_value(&response));
    }
}
