#include <atomic>
#include <iostream>
#include <string>

#include <ortools/sat/cp_model.h>
#include <ortools/sat/cp_model_checker.h>
#include <ortools/sat/cp_model_solver.h>
#include <ortools/sat/model.h>
#include <ortools/util/time_limit.h>

namespace sat = operations_research::sat;

extern "C" unsigned char*
cp_sat_wrapper_solve(
    unsigned char* model_buf,
    size_t model_size,
    size_t* out_size)
{
    sat::CpModelProto model;
    [[maybe_unused]] bool res = model.ParseFromArray(model_buf, model_size);
    assert(res);

    sat::CpSolverResponse response = sat::Solve(model);

    *out_size = response.ByteSizeLong();
    unsigned char* out_buf = (unsigned char*) malloc(*out_size);
    res = response.SerializeToArray(out_buf, *out_size);
    assert(res);

    return out_buf;
}

 extern "C" unsigned char*
 cp_sat_wrapper_solve_with_parameters(
     unsigned char* model_buf,
     size_t model_size,
     unsigned char* params_buf,
     size_t params_size,
     size_t* out_size)
 {
    sat::CpModelProto model;
    [[maybe_unused]] bool res = model.ParseFromArray(model_buf, model_size);
    assert(res);

    sat::SatParameters params;
    res = params.ParseFromArray(params_buf, params_size);
    assert(res);

    sat::CpSolverResponse response = sat::SolveWithParameters(model, params);

    *out_size = response.ByteSizeLong();
    unsigned char* out_buf = (unsigned char*) malloc(*out_size);
    res = response.SerializeToArray(out_buf, *out_size);
    assert(res);

    return out_buf;
}

extern "C" char*
cp_sat_wrapper_cp_model_stats(unsigned char* model_buf, size_t model_size) {
    sat::CpModelProto model;
    [[maybe_unused]] const bool res = model.ParseFromArray(model_buf, model_size);
    assert(res);

    const std::string stats = sat::CpModelStats(model);
    return strdup(stats.c_str());
}

extern "C" char*
cp_sat_wrapper_cp_solver_response_stats(
    unsigned char* response_buf,
    size_t response_size,
    bool has_objective)
{
    sat::CpSolverResponse response;
    [[maybe_unused]] const bool res = response.ParseFromArray(response_buf, response_size);
    assert(res);

    const std::string stats = sat::CpSolverResponseStats(response, has_objective);
    return strdup(stats.c_str());
}

extern "C" char*
cp_sat_wrapper_validate_cp_model(unsigned char* model_buf, size_t model_size) {
    sat::CpModelProto model;
    [[maybe_unused]] const bool res = model.ParseFromArray(model_buf, model_size);
    assert(res);

    const std::string stats = sat::ValidateCpModel(model);
    return strdup(stats.c_str());
}

extern "C" bool
cp_sat_wrapper_solution_is_feasible(
    unsigned char* model_buf,
    size_t model_size,
    const int64_t* solution_buf,
    size_t solution_size)
{
    sat::CpModelProto model;
    [[maybe_unused]] const bool res = model.ParseFromArray(model_buf, model_size);
    assert(res);

    std::vector<int64_t> variable_values;
    variable_values.reserve(solution_size);
    for (size_t i = 0; i < solution_size; ++i) {
        variable_values.push_back(solution_buf[i]);
    }

    return sat::SolutionIsFeasible(model, variable_values);
}

extern "C" unsigned char*
cp_sat_wrapper_solve_with_callback(
    const unsigned char* model_buf,
    size_t model_size,
    const unsigned char* params_buf,
    size_t params_size,
    const unsigned char* stop_flag,
    void* user_data,
    void (*solution_cb)(void* user_data, const unsigned char* resp_buf, size_t resp_size),
    size_t* out_size)
{
    static_assert(sizeof(std::atomic<bool>) == 1,
                  "std::atomic<bool> must be one byte to alias a Rust AtomicBool");
    static_assert(std::atomic<bool>::is_always_lock_free,
                  "std::atomic<bool> must be lock-free to alias a Rust AtomicBool");

    sat::CpModelProto model_proto;
    [[maybe_unused]] bool res = model_proto.ParseFromArray(model_buf, model_size);
    assert(res);

    sat::SatParameters params;
    res = params.ParseFromArray(params_buf, params_size);
    assert(res);

    sat::Model model;
    model.Add(sat::NewSatParameters(params));

    // Registering our boolean before any solver-internal ModelSharedTimeLimit is
    // built makes the solver adopt it as the shared stop signal for every worker
    // (see SharedTimeLimit's constructor in util/time_limit.h).
    if (stop_flag != nullptr) {
        std::atomic<bool>* flag =
            reinterpret_cast<std::atomic<bool>*>(const_cast<unsigned char*>(stop_flag));
        model.GetOrCreate<operations_research::TimeLimit>()
            ->RegisterExternalBooleanAsLimit(flag);
    }

    if (solution_cb != nullptr) {
        model.Add(sat::NewFeasibleSolutionObserver(
            [user_data, solution_cb](const sat::CpSolverResponse& response) {
                std::string buf;
                response.SerializeToString(&buf);
                solution_cb(user_data,
                            reinterpret_cast<const unsigned char*>(buf.data()),
                            buf.size());
            }));
    }

    sat::CpSolverResponse response = sat::SolveCpModel(model_proto, &model);

    *out_size = response.ByteSizeLong();
    unsigned char* out_buf = (unsigned char*) malloc(*out_size);
    res = response.SerializeToArray(out_buf, *out_size);
    assert(res);

    return out_buf;
}
