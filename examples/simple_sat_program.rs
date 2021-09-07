use cp_sat::proto::{
    constraint_proto::Constraint, AllDifferentConstraintProto, ConstraintProto, CpModelProto,
    IntegerVariableProto,
};

fn main() {
    let model = CpModelProto {
        variables: vec![
            IntegerVariableProto {
                name: "x".into(),
                domain: vec![0, 2],
            },
            IntegerVariableProto {
                name: "y".into(),
                domain: vec![0, 2],
            },
            IntegerVariableProto {
                name: "z".into(),
                domain: vec![0, 2],
            },
        ],
        constraints: vec![ConstraintProto {
            constraint: Some(Constraint::AllDiff(AllDifferentConstraintProto {
                vars: vec![0, 1, 2],
            })),
            ..Default::default()
        }],
        ..Default::default()
    };
    println!("{:#?}", model);

    println!("model stats: {}", cp_sat::cp_model_stats(&model));

    let response = cp_sat::solve(&model);
    println!("{:#?}", response);
    println!(
        "response stats: {}",
        cp_sat::cp_solver_response_stats(&response, false)
    );
}
