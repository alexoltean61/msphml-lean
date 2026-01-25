import Hybrid.BNF
import Hybrid.Language.Form

hybrid_def SMC :=
    sort Nat  ::= builtin Nat
    sort Bool ::= builtin Bool | "_==_"(Nat, Nat) | "_<=_"(Nat, Nat)

    sort Var  ::= builtin String
    sort AExp ::= subsort Nat | subsort Var
    sort AExp ::= "_+_"(AExp, AExp) | "++"(Var)
    sort BExp ::= "_<=_"(AExp, AExp)
    sort Stmt ::= skip
                | "_:=_"(Var, AExp)
                | "if_then_else_"(BExp, Stmt, Stmt)
                | "while_do_"(BExp, Stmt)
                | "_;_"(Stmt, Stmt)

    sort Val ::= subsort Nat | subsort Bool
    sort ValStack ::= nil
                | "_·_"(Val, ValStack)
    sort Mem ::= empty | "set"(Mem, Var, Nat)
    sort CtrlStack ::= "c"(AExp)              [cAExp]
                | "c"(BExp)                   [cBExp]
                | "c"(Stmt)                   [cStmt]
                | "asgn"(Var)
                | plus | leq
                | "_?"(Val)                   [PDLTest]
                | "_;_"(CtrlStack, CtrlStack) [PDLSeq]
                | "*"(CtrlStack)              [PDLStar]
    sort Config ::= "<_,_>"(ValStack, Mem)    [mkConfig]

#print SMC.Sorts
#print SMC.Ops
#print SMC.CtNoms
#print SMC
