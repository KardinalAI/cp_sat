use crate::proto;
use libc::c_char;
use prost::Message;
use std::ffi::CStr;
use std::ffi::c_void;

extern "C" {
    fn cp_sat_wrapper_solve(
        model_buf: *const u8,
        model_size: usize,
        out_size: &mut usize,
    ) -> *mut u8;
    fn cp_sat_wrapper_solve_with_parameters(
        model_buf: *const u8,
        model_size: usize,
        params_buf: *const u8,
        params_size: usize,
        out_size: &mut usize,
    ) -> *mut u8;
    fn cp_sat_wrapper_solve_with_parameters_and_handler(
        model_buf: *const u8,
        model_size: usize,
        params_buf: *const u8,
        params_size: usize,
        handler_caller: extern "C" fn(*const u8, usize, *mut c_void),
        handler: *mut c_void,
        out_size: &mut usize,
    ) -> *mut u8;
    fn cp_sat_wrapper_cp_model_stats(model_buf: *const u8, model_size: usize) -> *mut c_char;
    fn cp_sat_wrapper_cp_solver_response_stats(
        response_buf: *const u8,
        response_size: usize,
        has_objective: bool,
    ) -> *mut c_char;
    fn cp_sat_wrapper_validate_cp_model(model_buf: *const u8, model_size: usize) -> *mut c_char;
    fn cp_sat_wrapper_solution_is_feasible(
        model_buf: *const u8,
        model_size: usize,
        solution_buf: *const i64,
        solution_size: usize,
    ) -> bool;
}

/// Solves the given [CpModelProto][crate::proto::CpModelProto] and
/// returns an instance of
/// [CpSolverResponse][crate::proto::CpSolverResponse].
pub fn solve(model: &proto::CpModelProto) -> proto::CpSolverResponse {
    let mut buf = Vec::default();
    model.encode(&mut buf).unwrap();
    let mut out_size = 0;
    let res = unsafe { cp_sat_wrapper_solve(buf.as_ptr(), buf.len(), &mut out_size) };
    let out_slice = unsafe { std::slice::from_raw_parts(res, out_size) };
    let response = proto::CpSolverResponse::decode(out_slice).unwrap();
    unsafe { libc::free(res as _) };
    response
}

/// Solves the given [CpModelProto][crate::proto::CpModelProto] with
/// the given parameters.
pub fn solve_with_parameters(
    model: &proto::CpModelProto,
    params: &proto::SatParameters,
) -> proto::CpSolverResponse {
    let mut model_buf = Vec::default();
    model.encode(&mut model_buf).unwrap();
    let mut params_buf = Vec::default();
    params.encode(&mut params_buf).unwrap();

    let mut out_size = 0;
    let res = unsafe {
        cp_sat_wrapper_solve_with_parameters(
            model_buf.as_ptr(),
            model_buf.len(),
            params_buf.as_ptr(),
            params_buf.len(),
            &mut out_size,
        )
    };
    let out_slice = unsafe { std::slice::from_raw_parts(res, out_size) };
    let response = proto::CpSolverResponse::decode(out_slice).unwrap();
    unsafe { libc::free(res as _) };
    response
}

/// User provided solution handler that is called with feasible solutions.
pub type SolutionHandler = Box<dyn FnMut(proto::CpSolverResponse)>;

/// Solves the given [CpModelProto][crate::proto::CpModelProto] with
/// the given parameters,
/// and calls the [SolutionHandler] on each improving feasible solution found
/// during the search. For a non-optimization problem, if the option
/// [proto::SatParameters.enumerate_all_solutions] to find all
/// solutions was set, then this will be called on each new solution.
///
/// Please note that it does not work in parallel
/// (i. e. parameter [proto::SatParameters::num_search_workers] > 1).
pub fn solve_with_parameters_and_handler(
    model: &proto::CpModelProto,
    params: &proto::SatParameters,
    mut handler: SolutionHandler,
) -> proto::CpSolverResponse {
    let mut model_buf = Vec::default();
    model.encode(&mut model_buf).unwrap();
    let mut params_buf = Vec::default();
    params.encode(&mut params_buf).unwrap();

    let mut out_size = 0;
    let res = unsafe {
        cp_sat_wrapper_solve_with_parameters_and_handler(
            model_buf.as_ptr(),
            model_buf.len(),
            params_buf.as_ptr(),
            params_buf.len(),
            solution_handler_caller,
            &mut handler as *mut _ as *mut c_void,
            &mut out_size,
        )
    };
    let out_slice = unsafe { std::slice::from_raw_parts(res, out_size) };
    let response = proto::CpSolverResponse::decode(out_slice).unwrap();
    unsafe { libc::free(res as _) };
    response
}

/// Callback that is called from cpp code and transforms a buffered response to a
/// [proto::CpSolverResponse] that can be used by a [SolutionHandler].
///
/// # Arguments
/// - `response_buf` and `response_size`: buffer and size of a [proto::CpSolverResponse]
/// - `handler`: a user provided solution handler [SolutionHandler] that accepts a
///     [proto::CpSolverResponse]
extern "C" fn solution_handler_caller(response_buf: *const u8, response_size: usize, handler: *mut c_void) {
    let response_slice = unsafe {
        std::slice::from_raw_parts(response_buf, response_size)
    };
    let response = proto::CpSolverResponse::decode(response_slice).unwrap();
    unsafe { libc::free(response_buf as _) };

    unsafe {
        let tmp = handler as *mut SolutionHandler;
        (*tmp)(response);
    }
}

/// Returns a string with some statistics on the given
/// [CpModelProto][crate::proto::CpModelProto].
pub fn cp_model_stats(model: &proto::CpModelProto) -> String {
    let mut model_buf = Vec::default();
    model.encode(&mut model_buf).unwrap();
    let char_ptr = unsafe { cp_sat_wrapper_cp_model_stats(model_buf.as_ptr(), model_buf.len()) };
    let res = unsafe { CStr::from_ptr(char_ptr) }
        .to_str()
        .unwrap()
        .to_owned();
    unsafe { libc::free(char_ptr as _) };
    res
}

/// Returns a string with some statistics on the solver response.
///
/// If the second argument is false, we will just display NA for the
/// objective value instead of zero. It is not really needed but it
/// makes things a bit clearer to see that there is no objective.
pub fn cp_solver_response_stats(response: &proto::CpSolverResponse, has_objective: bool) -> String {
    let mut response_buf = Vec::default();
    response.encode(&mut response_buf).unwrap();
    let char_ptr = unsafe {
        cp_sat_wrapper_cp_solver_response_stats(
            response_buf.as_ptr(),
            response_buf.len(),
            has_objective,
        )
    };
    let res = unsafe { CStr::from_ptr(char_ptr) }
        .to_str()
        .unwrap()
        .to_owned();
    unsafe { libc::free(char_ptr as _) };
    res
}

/// Verifies that the given model satisfies all the properties
/// described in the proto comments. Returns an empty string if it is
/// the case, otherwise fails at the first error and returns a
/// human-readable description of the issue.
pub fn validate_cp_model(model: &proto::CpModelProto) -> String {
    let mut model_buf = Vec::default();
    model.encode(&mut model_buf).unwrap();
    let char_ptr = unsafe { cp_sat_wrapper_validate_cp_model(model_buf.as_ptr(), model_buf.len()) };
    let res = unsafe { CStr::from_ptr(char_ptr) }
        .to_str()
        .unwrap()
        .to_owned();
    unsafe { libc::free(char_ptr as _) };
    res
}

/// Verifies that the given variable assignment is a feasible solution
/// of the given model. The values vector should be in one to one
/// correspondence with the model.variables() list of variables.
///
/// # Example
///
/// ```
/// # use cp_sat::builder::CpModelBuilder;
/// # use cp_sat::proto::CpSolverStatus;
/// # use cp_sat::ffi::solution_is_feasible;
/// let mut model = CpModelBuilder::default();
/// let x = model.new_bool_var();
/// let y = model.new_bool_var();
/// model.add_and([x, y]);
/// assert!(solution_is_feasible(model.proto(), &[1, 1]));
/// assert!(!solution_is_feasible(model.proto(), &[1, 0]));
/// assert!(!solution_is_feasible(model.proto(), &[0, 1]));
/// assert!(!solution_is_feasible(model.proto(), &[0, 0]));
/// ```
pub fn solution_is_feasible(model: &proto::CpModelProto, solution: &[i64]) -> bool {
    let mut model_buf = Vec::default();
    model.encode(&mut model_buf).unwrap();
    unsafe {
        cp_sat_wrapper_solution_is_feasible(
            model_buf.as_ptr(),
            model_buf.len(),
            solution.as_ptr(),
            solution.len(),
        )
    }
}
