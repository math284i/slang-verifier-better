pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Ident,PrefixOp,ExprKind,Op};
use slang_ui::prelude::*;
use std::collections::HashSet;
pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate over domain items
        for d in file.domains() {

            // Iterate over functions
            for f in d.functions() {
                let f_smt = f.clone().smt()?;
                solver.declare_fun(&f_smt)?;
            }
            // Iterate over axioms
            for a in d.axioms() {
                let a_smt = a.clone().expr.smt()?;
                solver.assert(a_smt.as_bool()?)?;
            }
        }

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt()?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            let cmd = &m.body.clone().unwrap().cmd;
  
            let posts = m.ensures();

            let post_condition:Vec<(Expr, String)> = posts.map(|expr| (expr.clone(), "Error of post".to_string())).collect();
            
            let ivl = cmd_to_ivlcmd(cmd, &post_condition)?;
            let mut existing_names = HashSet::new();

            for (e,s) in swp(&ivl, &post_condition, &mut existing_names){
                println!("{e}");
                // Convert obligation to SMT expression
                let soblig = e.smt()?;

                // Run the following solver-related statements in a closed scope.
                // That is, after exiting the scope, all assertions are forgotten
                // from subsequent executions of the solver
                solver.scope(|solver| {
                    // Check validity of obligation
                    solver.assert(!soblig.as_bool()?)?;
                    // Run SMT solver on all current assertions
                    match solver.check_sat()? {
                        // If the obligations result not valid, report the error (on
                        // the span in which the error happens)
                        smtlib::SatResult::Sat => {
                            cx.error(e.span, format!("{s}"));
                        }
                        smtlib::SatResult::Unknown => {
                            cx.warning(e.span, format!("{s}: unknown sat result"));
                        }
                        smtlib::SatResult::Unsat => (),
                    }
                    Ok(())
                })?;
            }
        }
        Ok(())
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(
    cmd: &Cmd,
    post_condition: &Vec<(Expr, String)>,
) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Seq(cmd1, cmd2) => {
            let ivl1 = cmd_to_ivlcmd(cmd1, post_condition)?;
            let ivl2 = cmd_to_ivlcmd(cmd2, post_condition)?;
            Ok(IVLCmd {
                span: cmd.span.clone(),
                kind: IVLCmdKind::Seq(Box::new(ivl1), Box::new(ivl2)),
            })
        }
        CmdKind::Assert { condition, .. } => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Assume { condition } => Ok(IVLCmd::assume(condition)),
        CmdKind::VarDefinition { name, ty, expr } => {
            if let Some(expr) = expr {
                Ok(IVLCmd {
                    span: cmd.span.clone(),
                    kind: IVLCmdKind::Seq(
                        Box::new(IVLCmd::havoc(name, &ty.1)),
                        Box::new(IVLCmd::assign(name, expr)),
                    ),
                })
            } else {
                Ok(IVLCmd::havoc(name, &ty.1))
            }
        }
        CmdKind::Assignment { name, expr } => {
            
             if let ExprKind::Infix(_, Op::Div, rhs) = &expr.kind {
                // Insert an assert to check that the divisor is not zero
                let div_by_zero_check = IVLCmd::assert(
                    &Expr::new_typed( ExprKind::Infix(rhs.clone(), Op::Ne, Box::new(Expr::num(0))), expr.ty.clone()),
                    "Division by zero detected",
                );
                Ok(IVLCmd::seq(&div_by_zero_check, &IVLCmd::assign(name, expr)))
            } else { 
                Ok(IVLCmd::assign(name, expr))
            }
        },
        CmdKind::Match { body } => {
            let mut cases: Vec<IVLCmd> = vec![];
            for case in &body.cases {
                let condition = IVLCmd::assume(&case.condition);
                let cmd = cmd_to_ivlcmd(&case.cmd, post_condition)?;
                cases.push(IVLCmd::seq(&condition, &cmd));
            }
            Ok(IVLCmd::nondets(&cases))
        }
        CmdKind::Return { expr } => {
            let mut ivl_cmds = Vec::new();
            ivl_cmds.push(IVLCmd::return_ivl(expr));
            for (post_expr, msg) in post_condition.iter() {
                ivl_cmds.push(IVLCmd::assert(post_expr, msg));
            }


            ivl_cmds.push(IVLCmd::assume(&Expr::bool(false)));

            Ok(IVLCmd::seqs(&ivl_cmds))
        }
        CmdKind::Loop {
            invariants, body, ..} => {
            let mut ivl_cmds: Vec<IVLCmd> = Vec::new();
            let mut case_bodies = Vec::new();
            let mut all_conditions = Expr::bool(true);
            let mut all_invariants = Expr::bool(true);
            for inv in invariants {
                all_invariants = all_invariants.and(&inv);
            }

            //First assert invariants
            ivl_cmds.push(IVLCmd::assert(&all_invariants,"Loop invariants might not hold before the loop"));
            
            //Havoc chars, to emulate all possible inputs
            let vars = cmd.clone().assigned_vars();
            for var in vars {
                ivl_cmds.push(IVLCmd::havoc(&var.0, &var.1));
            }
            
            //Assume invariants, to make sure the havoc stays in the scope of invariants.
            ivl_cmds.push(IVLCmd::assume(&all_invariants));

            //Creating all conditions and encodings for C
            for case in &body.cases {
                all_conditions = all_conditions.and(&case.condition);

                case_bodies.push(cmd_to_ivlcmd(&case.cmd, post_condition)?); 
            }

            let if_body1 = IVLCmd::seq(&IVLCmd::assume(&all_conditions),
                                                &IVLCmd::seqs(&case_bodies));
            let if_body2 = IVLCmd::seq(&IVLCmd::assert(&all_invariants, "Loop invariants might not hold during the loop"),
                                                &IVLCmd::assume(&Expr::bool(false)));
            let if_body_complete = IVLCmd::seq(&if_body1, &if_body2);

            let if_else_body = IVLCmd::nondet(&if_body_complete, &IVLCmd::assume(&all_conditions.prefix(PrefixOp::Not)));
            // Pushed the if else IVL command to the stack.
            ivl_cmds.push(if_else_body);

            Ok(IVLCmd::seqs(&ivl_cmds))
        }

        _ => todo!("Not supported (yet). cmd_to_ivlcmd"),
    }
}


fn get_new_non_existing_name(existing_names: &HashSet<String>) -> String {
    let mut counter = 0;
    loop {
        let new_name = format!("expr{}", counter);
        if !existing_names.contains(&new_name) {
            return new_name;
        }
        counter += 1;
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn swp(
    ivl: &IVLCmd,
    post_condition: &Vec<(Expr, String)>,
    existing_names: &mut HashSet<String>,
) -> Vec<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Seq(ivl1, ivl2) => {
            let wp2 = swp(ivl2, post_condition, existing_names);
            let wp1 = swp(ivl1, &wp2, existing_names);
            wp1 // Return combined result
        }
        IVLCmdKind::Assume { condition } => {
            // Process each element in post_condition and apply implication
            let mut new_post_conditions = Vec::new();
            for (expr, msg) in post_condition {
                let new_expr = condition.clone().imp(&expr.clone()).with_span(expr.span);
                let new_msg = format!("{} => {}", expr, msg);
                new_post_conditions.push((new_expr, new_msg));
            }
            new_post_conditions
        }
        IVLCmdKind::Assert { condition, message } => {
            let mut new_post_conditions = post_condition.clone();
            new_post_conditions.push((condition.clone(), message.clone()));
            new_post_conditions
        }
        IVLCmdKind::Havoc { name, ty } => {
            let new_name = get_new_non_existing_name(existing_names);
            existing_names.insert(new_name.clone());
            let ident = Ident(new_name.clone());

            let new_expr = Expr::ident(&ident, ty);
            post_condition
                .iter()
                .map(|(expr, msg)| (expr.clone().subst_ident(&name.ident, &new_expr).with_span(expr.span), msg.clone()))
                .collect()
        }
        IVLCmdKind::Assignment { expr, name } => post_condition
            .iter()
            .map(|(cond_expr, msg)| {
                (cond_expr.clone().subst_ident(&name.ident, expr).with_span(cond_expr.span), msg.clone())
            })
            .collect(),
        IVLCmdKind::NonDet(ivl1, ivl2) => {
            let wp1 = swp(ivl1, post_condition, existing_names);
            let wp2 = swp(ivl2, post_condition, existing_names);
            wp1.into_iter()
                .chain(wp2.into_iter())
                .collect() // Combine both branches
        }
        IVLCmdKind::Return { expr } => match expr {
            Some(e) => post_condition
                .iter()
                .map(|(cond_expr, msg)| (cond_expr.clone().subst_result(e).with_span(cond_expr.span), msg.clone()))
                .collect(),
            None => post_condition.clone(),
        }
        _ => todo!("Not supported (yet). wp for {:?}", ivl),
    }
}