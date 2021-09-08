use libc::c_char;
use prost::Message;
use std::ffi::CStr;

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/operations_research.sat.rs"));
}
pub mod builder;

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
    fn cp_sat_wrapper_cp_model_stats(model_buf: *const u8, model_size: usize) -> *mut c_char;
    fn cp_sat_wrapper_cp_solver_response_stats(
        response_buf: *const u8,
        response_size: usize,
        has_objective: bool,
    ) -> *mut c_char;
}

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
