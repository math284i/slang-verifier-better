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
            // Get method's preconditions and combine them
            let pre = m.requires()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            
            // Convert precondition to SMT and assert it
            let spre = pre.smt()?;
            solver.assert(spre.as_bool()?)?;
    
            // Get method's body and convert it to IVL
            let cmd = &m.body.clone().unwrap().cmd;
            let ivl = cmd_to_ivlcmd(cmd)?;
    
            // Get method's postconditions and combine them
            let post = m.ensures()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            
            let mut existing_names = HashSet::new();
            let mut spanlist: Vec<(Expr, String)> = Vec::new(); // Initialize as a vector of `(Expr, String)` pairs
    
            // Call `swp`, which now returns a `Vec<(Expr, String)>`
            let obligations = swp(&ivl, &mut spanlist, &mut existing_names);
    
            // Iterate over each `(Expr, String)` in the obligations list
            for (obligation_expr, msg) in obligations {
                // Convert obligation to SMT expression
                let soblig = obligation_expr.smt()?;
    
                // Use the solver within a closed scope for each obligation
                solver.scope(|solver| {
                    // Check validity of the obligation
                    solver.assert(!soblig.as_bool()?)?;
                    
                    match solver.check_sat()? {
                        smtlib::SatResult::Sat => {
                            // If the obligation is not valid, report the error with its message
                            cx.error(obligation_expr.span, msg.clone());
                        }
                        smtlib::SatResult::Unknown => {
                            cx.warning(obligation_expr.span, format!("{msg}: unknown sat result"));
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
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Seq(cmd1, cmd2) => {
            let ivl1 = cmd_to_ivlcmd(cmd1)?;
            let ivl2 = cmd_to_ivlcmd(cmd2)?;
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
                let cmd = cmd_to_ivlcmd(&case.cmd)?;
                cases.push(IVLCmd::seq(&condition, &cmd));
            }
            Ok(IVLCmd::nondets(&cases))
        }
        CmdKind::Return { expr } => Ok(IVLCmd::return_ivl(expr)),

        CmdKind::Loop {
            invariants, body, ..
        } => {
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
            //if(b) But push the whole body as ivl
            for case in &body.cases {
                let condition = IVLCmd::assume(&case.condition);
                ivl_cmds.push(condition);

                let encoded_cmd = cmd_to_ivlcmd(&case.cmd)?;
                ivl_cmds.push(encoded_cmd);

                for inv in invariants {
                    ivl_cmds.push(IVLCmd::assert(
                        inv,
                        "Loop invariant doesn't hold during the loop.",
                    ));
                }
            }

            //If an invariant fails beforehand, this will discard any paths that fail.
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
    post_condition: &mut Vec<(Expr, String)>,
    existing_names: &mut HashSet<String>,
) -> Vec<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Seq(ivl1, ivl2) => {
            if let IVLCmdKind::Return { .. } = ivl1.kind {
                post_condition.push((
                    Expr::bool(false),
                    String::from("Return statement found in the middle of a sequence! Return must be the last command.")
                ));
                return post_condition.clone();
            }

            swp(ivl2, post_condition, existing_names);
            swp(ivl1, post_condition, existing_names);
            post_condition.clone()
        }
        IVLCmdKind::Assume { condition } => {
            // Create a single conjunction of all expressions in `post_condition`
            let combined_expr = post_condition.iter()
                .fold(condition.clone(), |acc, (expr, _)| acc.imp(&expr.clone()));

            post_condition.push((
                combined_expr,
                format!("{} => {:?}", condition, post_condition),
            ));
            return post_condition.clone();
        }
        IVLCmdKind::Assert { condition, message } => {
            // Create a single conjunction of all expressions in `post_condition`
            let combined_expr = post_condition.iter()
                .fold(condition.clone(), |acc, (expr, _)| acc.and(&expr.clone()));

            post_condition.push((
                combined_expr,
                message.clone(),
            ));
            return post_condition.clone();
        }
        IVLCmdKind::Havoc { name, ty } => {
            let new_name = GetNewNonExistingName(existing_names);
            existing_names.insert(new_name.clone());
            let ident = Ident(new_name.clone());
            let new_expr = Expr::ident(&ident, &ty);

            let updated_exprs: Vec<Expr> = post_condition.iter()
                .map(|(expr, _)| expr.subst_ident(&name.ident, &new_expr))
                .collect();
            
            for expr in updated_exprs {
                post_condition.push((
                    expr,
                    format!("Havoc: variable {} replaced with {}", name.ident, new_name),
                ));
            }
            return post_condition.clone();
        }
        IVLCmdKind::Assignment { expr, name } => {
            let updated_exprs: Vec<Expr> = post_condition.iter()
                .map(|(p_expr, _)| p_expr.subst_ident(&name.ident, expr))
                .collect();

            for expr in updated_exprs {
                post_condition.push((
                    expr.clone(),
                    format!("{} := {}", name, expr),
                ));
            }
            return post_condition.clone();
        }
        IVLCmdKind::NonDet(ivl1, ivl2) => {
            let msg1;
            let msg2;

            swp(ivl1, post_condition, existing_names);
            msg1 = post_condition.last().map(|(_, msg)| msg.clone()).unwrap_or_default();

            swp(ivl2, post_condition, existing_names);
            msg2 = post_condition.last().map(|(_, msg)| msg.clone()).unwrap_or_default();

            let expr1 = post_condition.iter().map(|(expr, _)| expr.clone()).last().unwrap();
            let expr2 = post_condition.iter().map(|(expr, _)| expr.clone()).last().unwrap();

            post_condition.push((
                expr1.and(&expr2),
                format!("Msg1: {}, Msg2: {}", msg1, msg2),
            ));
            return post_condition.clone();
        }
        IVLCmdKind::Return { expr } => {
            match expr {
                Some(e) => {
                    let updated_exprs: Vec<Expr> = post_condition.iter()
                        .map(|(p_expr, _)| p_expr.subst_result(e))
                        .collect();

                    for expr in updated_exprs {
                        post_condition.push((
                            expr,
                            format!("Couldn't return type {}", e),
                        ));
                    }
                }
                None => {
                    let last_expr = post_condition.last().map(|(expr, _)| expr.clone()).unwrap();
                    post_condition.push((
                        last_expr,
                        String::from("Return without type failed"),
                    ));
                }
            }
            return post_condition.clone();
        }
        _ => todo!("{}", format!("Not supported (yet). wp for {}", ivl)),
    }
}

