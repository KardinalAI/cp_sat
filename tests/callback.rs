use std::sync::atomic::AtomicBool;

use cp_sat::builder::{CpModelBuilder, LinearExpr};
use cp_sat::proto::{CpSolverStatus, SatParameters};

#[test]
fn reports_solutions_and_returns_optimal() {
    let mut model = CpModelBuilder::default();
    let xs: Vec<_> = (0..20).map(|_| model.new_bool_var()).collect();
    model.maximize(xs.iter().copied().collect::<LinearExpr>());

    let mut count = 0;
    let response = model.solve_with_callback(&SatParameters::default(), None, |_| count += 1);

    assert_eq!(response.status(), CpSolverStatus::Optimal);
    assert!(count >= 1, "expected at least one improving solution");
}

#[test]
fn preset_stop_flag_does_not_hang() {
    let mut model = CpModelBuilder::default();
    let xs: Vec<_> = (0..40).map(|_| model.new_bool_var()).collect();
    model.maximize(xs.iter().copied().collect::<LinearExpr>());

    let stop = AtomicBool::new(true);
    let mut params = SatParameters::default();
    params.max_time_in_seconds = Some(60.0);

    let response = model.solve_with_callback(&params, Some(&stop), |_| {});

    assert!(
        response.wall_time < 10.0,
        "a pre-set stop flag should make the solver return promptly, not run to the cap"
    );
}

#[test]
fn callback_panic_propagates_to_caller() {
    let mut model = CpModelBuilder::default();
    let x = model.new_bool_var();
    model.maximize(x);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        model.solve_with_callback(&SatParameters::default(), None, |_| panic!("boom"));
    }));

    assert!(
        result.is_err(),
        "a panic inside the callback must be re-raised on the calling thread"
    );
}
