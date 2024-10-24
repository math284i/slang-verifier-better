pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr};
use slang_ui::{prelude::*, Report};


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
            let ivl = cmd_to_ivlcmd(cmd)?;
            // Calculate obligation and error message (if obligation is not
            // verified)
            
            // Get method's postconditions:
            let posts = m.ensures();
            // Merge them into a single condition
            let post = posts
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            let (oblig, msg) = wp(&ivl, &post)?;
            // Convert obligation to SMT expression
            let soblig = oblig.smt()?;

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
                        cx.error(oblig.span, format!("{msg}"));
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, "{msg}: unknown sat result");
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
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
        },
        CmdKind::Assert { condition, .. } => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Assume { condition } => Ok(IVLCmd::assume(condition)),
        CmdKind::VarDefinition { name, ty, expr } => {
            if let Some(expr) = expr {
                Ok(IVLCmd::assign(name, expr))
            } else {
                Ok(IVLCmd::havoc(name, &ty.1))
            }
        },
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
        CmdKind::Match { body } => {
            let mut cases: Vec<IVLCmd> = vec![];
            for case in &body.cases {
                let condition = IVLCmd::assume(&case.condition);
                let cmd = cmd_to_ivlcmd(&case.cmd)?;
                cases.push(IVLCmd::seq(&condition, &cmd));
            }
            Ok(IVLCmd::nondets(&cases))
        },
        CmdKind::Return { expr } => Ok(IVLCmd::return_ivl(expr)),

        CmdKind::Loop { invariants, body, .. } => {
            let mut ivl_invs: Vec<IVLCmd> = Vec::new();
            for inv in invariants {
                ivl_invs.push(IVLCmd::assume(inv));  // Assume  before loop iteration
            }
        
            let mut ivl_seq: Vec<IVLCmd> = ivl_invs; // Loop seq in vector
        
            for case in &body.cases {
                let ivl_body = cmd_to_ivlcmd(&case.cmd)?;  // Convert each body case into an IVL command
        

                // Assert the actual invariant before the loop body
                for inv in invariants {
                    ivl_seq.push(IVLCmd::assert(inv, "Invariant doesn't hold before iteration"));  // Check invariant before iteration
                }
        
                ivl_seq.push(ivl_body);
        
                // Assert the actual invariant after the loop body
                for inv in invariants {
                    ivl_seq.push(IVLCmd::assert(inv, "Invariant doesn't hold after iteration"));  // Check invariant after iteration
                }
            }
        
            // Assert that the loop has been verified
            let loop_end = IVLCmd::assert(&Expr::bool(true), "Loop not verified");
        
            ivl_seq.push(loop_end);  //Combine the loop sequence and last assertion
        
            return Ok(IVLCmd::seqs(&ivl_seq));  // Combine all commands into a sequence
        }
        
        
        
        
        _ => todo!("Not supported (yet). cmd_to_ivlcmd"),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, post_condition: &Expr) -> Result<(Expr, String)> {  
    match &ivl.kind {
        IVLCmdKind::Seq(ivl1, ivl2) => {
            if let IVLCmdKind::Return { .. } = ivl1.kind {
                return Ok((Expr::bool(false),
                    format!("Return statement found in the middle of a sequence! Return must be the last command.")
                ));
            }

            let (wp2, msg2) = wp(ivl2, post_condition)?;
            let (wp1, msg1) = wp(ivl1, &wp2)?;
            Ok((wp1, format!("msg2: {}", msg2)))
        }
        IVLCmdKind::Assume { condition } => Ok((condition.clone().imp(post_condition) , format!("{} => {}", condition, post_condition))),
        IVLCmdKind::Assert { condition, message } => Ok((condition.clone() & post_condition.clone(), message.clone())),
        IVLCmdKind::Havoc { name, ty } => Ok((post_condition.clone(), "Havoc".to_string())),
        IVLCmdKind::Assignment { expr, name } => Ok((post_condition.subst_ident(&name.ident, expr), format!("{} := {}", name, expr))),
        IVLCmdKind::NonDet(ivl1, ivl2) => {
            let (wp1, msg1) = wp(ivl1, post_condition)?;
            let (wp2, msg2) = wp(ivl2, post_condition)?;
            Ok((wp1.clone().and(&wp2), format!("Msg1: {}, msg2: {}", msg1, msg2)))
        },
        IVLCmdKind::Return { expr } => {
            match expr {
                Some(e) => Ok((post_condition.subst_result(e), format!("couldnt return type {}", e))),
                None           => Ok((post_condition.clone(), format!("Return without type failed")))
        IVLCmdKind::Assume { condition } => Ok((condition.clone().imp(post_condition), format!("{} & {}", condition, post_condition))),
        _ => todo!("{}", format!("Not supported (yet). wp for {}", ivl)),
    }
}