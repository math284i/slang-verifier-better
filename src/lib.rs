pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::{
    ast::{Cmd, CmdKind, Expr, ExprKind, Ident},
    Span,
};
use slang_ui::{
    prelude::{slang::ast::Name, *},
    Report,
};
use std::{collections::HashSet, iter::SkipWhile};
use tracing::span;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

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

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL

            // Calculate obligation and error message (if obligation is not
            // verified)

            // Get method's postconditions:
            let posts = m.ensures();
            // Merge them into a single condition
            let post:Vec<(Expr, String)> = posts.map(|expr| (expr.clone(), "Error of post".to_string())).collect();
            let ivl = cmd_to_ivlcmd(cmd, &post)?;
            let mut existing_names = HashSet::new();

            for (e,s) in swp(&ivl, &post, &mut existing_names){

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
    post_condition: &Vec<(Expr, String)>, // post_condition tilføjet her
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
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
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

            for (post_expr, msg) in post_condition.iter() {
                ivl_cmds.push(IVLCmd::assert(post_expr, msg));
            }

            ivl_cmds.push(IVLCmd::return_ivl(expr));

            ivl_cmds.push(IVLCmd::assume(&Expr::bool(false)));

            Ok(IVLCmd::seqs(&ivl_cmds))
        }
        CmdKind::Loop {
            invariants, body, ..} => {
            let mut ivl_cmds: Vec<IVLCmd> = Vec::new();

            for inv in invariants {
                ivl_cmds.push(IVLCmd::assert(
                    inv,
                    "Loop invariant doesn't hold before the loop.",
                ));
            }
            let vars = cmd.clone().assigned_vars();
            for var in vars {
                ivl_cmds.push(IVLCmd::havoc(&var.0, &var.1));
            }
            for inv in invariants {
                ivl_cmds.push(IVLCmd::assume(inv));
            }
            // Hvis b, push hele body som ivl
            for case in &body.cases {
                let condition = IVLCmd::assume(&case.condition);
                ivl_cmds.push(condition);

                let encoded_cmd = cmd_to_ivlcmd(&case.cmd, post_condition)?; 
                ivl_cmds.push(encoded_cmd);

                for inv in invariants {
                    ivl_cmds.push(IVLCmd::assert(
                        inv,
                        "Loop invariant doesn't hold during the loop.",
                    ));
                }
            }

            // Hvis et invariant fejler tidligere, vil dette kassere de stier, der fejler.
            ivl_cmds.push(IVLCmd::assume(&Expr::bool(false)));
            Ok(IVLCmd::seqs(&ivl_cmds))
        }

        _ => todo!("Not supported (yet). cmd_to_ivlcmd"),
    }
}


fn GetNewNonExistingName(existing_names: &HashSet<String>) -> String {
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

//TODO: skal laves om til swp (set weakest precondition, men brug liste fordi sets er weird - hjælpelæreren)
//TODO: Vi skal ved hver commando, have ændret det span den ligesom bruger
//, her kan man bruge commando, with_span, hvor man kan vælge om det er venstre eller højre side af sin kommando man vil have tjkket (det er så typisk højre)

//TODO: Alle ok skal laves om til return post_condition.push(Expr med det rigtige span)
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
                let new_expr = condition.clone().imp(&expr.clone());
                let new_msg = format!("{} => {}", condition, msg);
                new_post_conditions.push((new_expr, new_msg));
            }
            new_post_conditions
        }
        IVLCmdKind::Assert { condition, message } => {
            let mut post = post_condition.clone();
            post.push((condition.clone(), message.clone()));
            post
        }
        IVLCmdKind::Havoc { name, ty } => {
            let new_name = GetNewNonExistingName(existing_names);
            existing_names.insert(new_name.clone());
            let ident = Ident(new_name.clone());

            let new_expr = Expr::ident(&ident, ty);
            post_condition
                .iter()
                .map(|(expr, msg)| (expr.clone().subst_ident(&name.ident, &new_expr), msg.clone()))
                .collect()
        }
        IVLCmdKind::Assignment { expr, name } => post_condition
            .iter()
            .map(|(cond_expr, msg)| {
                (cond_expr.clone().subst_ident(&name.ident, expr), msg.clone())
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
                .map(|(cond_expr, msg)| (cond_expr.clone().subst_result(e), msg.clone()))
                .collect(),
            None => post_condition.clone(),
        },
        _ => todo!("Not supported (yet). wp for {:?}", ivl),
    }
}