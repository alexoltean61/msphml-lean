import Hybrid.BNF
import Hybrid.Language.Form

hybrid_def SMC :=
    sort Nat  ::= builtin Nat
    sort Bool ::= builtin Bool | "_==_"(Nat, Nat) | "_<=_"(Nat, Nat)

    sort Var  ::= builtin String
    sort AExp ::= subsort Nat | subsort Var
    sort AExp ::= "_+_"(AExp, AExp) | "++"(Var)
    sort BExp ::= "_<=_"(AExp, AExp)                [Leq]
    sort Stmt ::= skip
                | "_:=_"(Var, AExp)
                | "if_then_else_"(BExp, Stmt, Stmt) [IteStmt]
                | "while_do_"(BExp, Stmt)           [WhileStmt]
                | "_;_"(Stmt, Stmt)                 [SeqStmt]

    sort Val ::= subsort Nat | subsort Bool
    sort ValStack ::= nil
                | "_·_"(Val, ValStack)        [consValStack]
    sort Mem ::= empty | "set"(Mem, Var, Val)
    sort CtrlStack ::= "c"(AExp)              [cAExp]
                | "c"(BExp)                   [cBExp]
                | "c"(Stmt)                   [cStmt]
                | "asgn"(Var)
                | plus | leq
                | "_?"(Val)                   [PDLTest]
                | "_∪_"(CtrlStack, CtrlStack) [PDLUnion]
                | "_;_"(CtrlStack, CtrlStack) [PDLSeq]
                | "*"(CtrlStack)              [PDLStar]
    sort Config ::= "<_,_>"(ValStack, Mem)    [mkConfig]
                | "[_]_"(CtrlStack, Config)   [PDLOp]

abbrev SMCFormL := FormL SMC
abbrev SMCForm  := Form SMC

instance : Coe ℕ (SMCForm SMC.Nat) where
  coe := λ n => ℋNom (.ctNom ⟨toString n, ⟨n, rfl⟩⟩)
instance : Coe Bool (SMCForm SMC.Bool) where
  coe := λ b =>
    ℋNom (.ctNom  ⟨toString b, by cases b <;> simp⟩)

namespace SMC
/-
  Subsort operators probably also require some specific axioms
  (to the extent of, e.g., nat2AEXp's accessibility relation
  is an injective function)
-/
instance : Coe (SMCForm Nat) (SMCForm AExp) where
  coe := λ n => ℋ⟨nat2AExp⟩ n
instance : Coe (SMCForm Nat) (SMCForm Val) where
  coe := λ n => ℋ⟨nat2Val⟩ n
instance : OfNat (SMCForm AExp) n where
  ofNat := ℋ⟨nat2AExp⟩ n
instance : Coe (SMCForm Var) (SMCForm AExp) where
  coe := λ v => ℋ⟨var2AExp⟩ v
instance : Coe (SMCForm Bool) (SMCForm Val) where
  coe := λ b => ℋ⟨bool2Val⟩ b
instance : Coe (CtNoms s) (SMCForm s) where
  coe := λ c => FormL.nom (.ctNom c)

class Evaluable (α : Type u) where
  ctrlStackEval : α → SMCForm CtrlStack

instance : Evaluable (SMCForm AExp) where
  ctrlStackEval := FormL.appl cAExp
instance : Evaluable (SMCForm BExp) where
  ctrlStackEval := FormL.appl cBExp
instance : Evaluable (SMCForm Stmt) where
  ctrlStackEval := FormL.appl cStmt
instance : Evaluable (CtNoms Stmt) where
  ctrlStackEval c := FormL.appl cStmt c
instance : Evaluable ℕ where
  ctrlStackEval := λ n => FormL.appl cAExp n
instance : Evaluable (SMCForm Var) where
  ctrlStackEval := λ x => FormL.appl cAExp x

class HasSeq (α : Type u) where
  seq : α → α → α
instance : HasSeq (SMCForm Stmt) where
  seq := λ s1 s2 => FormL.appl SeqStmt (FormL.cons s1 s2)
instance : HasSeq (SMCForm CtrlStack) where
  seq := λ c1 c2 => FormL.appl PDLSeq (FormL.cons c1 c2)

notation:100 s1:99 ";" s2:100 => HasSeq.seq s1 s2
notation:100 "c" "(" φ:100 ")" => Evaluable.ctrlStackEval φ
notation:100 "⟨" vs ", " mem "⟩" => ℋ⟨mkConfig⟩ (vs, mem)
-- Note!: [α] φ = ¬ ⟨α⟩ ¬ φ
notation:100 "[" ctrl "]" config => ℋ⟨PDLOp⟩ᵈ (∼ctrl, config)
notation:100 "asgn" "(" x ")" => ℋ⟨SMC.asgnVar_CtrlStack⟩ x
notation:100 x:101 "::=" a:101 => ℋ⟨SMC.«_:=_Var_AExp_Stmt»⟩ (x, a)
notation:100 "if" bexp "then" s1 "else" s2 "endif" => ℋ⟨IteStmt⟩ (bexp, s1, s2)
notation:100 "while" bexp "do'" s => ℋ⟨WhileStmt⟩ (bexp, s)
notation:100 c1 "∪" c2 => ℋ⟨PDLUnion⟩ (c1, c2)
notation:100 c1"*" => ℋ⟨PDLStar⟩ c1
notation:100 c1"?" => ℋ⟨PDLTest⟩ c1
notation:100 v:99 "⬝" vs:100 => ℋ⟨consValStack⟩ (v, vs)
notation:100 "set" "(" mem ", "  x ", "  n ")" => ℋ⟨setMem_Var_Val_Mem⟩ (mem, x, n)
notation:102 "++" x:101 => ℋ⟨«++Var_AExp»⟩ x
notation:102 a1:99 "+" a2:100 => ℋ⟨«_+_AExp_AExp_AExp»⟩ (a1, a2)
notation:100 a1:99 "<=" a2:100 => ℋ⟨Leq⟩ (a1, a2)

end SMC
