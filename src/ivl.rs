use slang::{
    ast::{Expr, Name, Type},
    Span,
};
use slang_ui::prelude::*;

#[derive(Debug, Clone)]
pub struct IVLCmd {
    pub span: Span,
    pub kind: IVLCmdKind,
}

#[derive(Debug, Clone)]
pub enum IVLCmdKind {
    Assignment { name: Name, expr: Expr },
    Havoc { name: Name, ty: Type },

    Assume { condition: Expr },
    Assert { condition: Expr, message: String },
    Return { expr: Option<Expr>},
    
    Seq(Box<IVLCmd>, Box<IVLCmd>),
    NonDet(Box<IVLCmd>, Box<IVLCmd>),
}