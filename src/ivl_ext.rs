use slang::{
    ast::{Expr, Name, Type},
    Span,
};
use slang_ui::prelude::*;

use crate::ivl::{IVLCmd, IVLCmdKind};

impl IVLCmd {
    pub fn assign(name: &Name, expr: &Expr) -> IVLCmd {
        IVLCmd {
            span: expr.span,
            kind: IVLCmdKind::Assignment {
                name: name.clone(),
                expr: expr.clone(),
            },
        }
    }
    pub fn seq(&self, other: &IVLCmd) -> IVLCmd {
        IVLCmd {
            span: Span::union(self.span, other.span),
            kind: IVLCmdKind::Seq(Box::new(self.clone()), Box::new(other.clone())),
        }
    }
    pub fn seqs(cmds: &[IVLCmd]) -> IVLCmd {
        cmds.iter()
            .cloned()
            .reduce(|a, b| IVLCmd::seq(&a, &b))
            .unwrap_or(IVLCmd::nop())
    }

    pub fn nondet(&self, other: &IVLCmd) -> IVLCmd {
        IVLCmd {
            span: Span::default(),
            kind: IVLCmdKind::NonDet(Box::new(self.clone()), Box::new(other.clone())),
        }
    }

    pub fn nondets(cmds: &[IVLCmd]) -> IVLCmd {
        cmds.iter()
            .cloned()
            .reduce(|a, b| IVLCmd::nondet(&a, &b))
            .unwrap_or(IVLCmd::unreachable())
    }
    pub fn assume(condition: &Expr) -> IVLCmd {
        IVLCmd {
            span: condition.span,
            kind: IVLCmdKind::Assume {
                condition: condition.clone(),
            },
        }
    }
    pub fn assert(condition: &Expr, message: &str) -> IVLCmd {
        IVLCmd {
            span: condition.span,
            kind: IVLCmdKind::Assert {
                condition: condition.clone(),
                message: message.to_owned(),
            },
        }
    }
    pub fn havoc(name: &Name, ty: &Type) -> IVLCmd {
        IVLCmd {
            kind: IVLCmdKind::Havoc {
                name: name.clone(),
                ty: ty.clone(),
            },
            span: Span::default(),
        }
    }

    pub fn return_ivl(expr: &Option<Expr>) -> IVLCmd {
        if let Some(expr_s) = expr {
            IVLCmd { 
                span: expr_s.span,  
                kind: IVLCmdKind::Return { 
                        expr: expr.clone() 
                } 
            }
        } else {
            IVLCmd { 
                span: Span::default(),
                kind: IVLCmdKind::Return { 
                        expr: expr.clone() 
                } 
            }
        }
    }

    pub fn nop() -> IVLCmd {
        IVLCmd::assume(&Expr::bool(true))
    }
    pub fn unreachable() -> IVLCmd {
        IVLCmd::assume(&Expr::bool(false))
    }
}

impl std::fmt::Display for IVLCmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            IVLCmdKind::Assignment { name, expr } => write!(f, "{} := {}", name, expr),
            IVLCmdKind::Havoc { name, .. } => write!(f, "havoc {}", name),
            IVLCmdKind::Assume { condition } => write!(f, "assume {}", condition),
            IVLCmdKind::Assert { condition, .. } => write!(f, "assert {}", condition),
            IVLCmdKind::Seq(c1, c2) => write!(f, "{} ; {}", c1, c2),
            IVLCmdKind::NonDet(c1, c2) => write!(f, "{{ {} }} [] {{ {} }}", c1, c2),
            IVLCmdKind::Return { expr } => {
                match expr {
                    Some(e) => write!(f, "return with {}", e),
                    None           => write!(f, "return without") 
                }
            }
        }
    }
}