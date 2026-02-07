import Hybrid.BNF
import Hybrid.Language

hybrid_def SMC :=
    sort Nat  ::= builtin Nat
                | "_+_"(Nat, Nat) [PlusNat]
                | "_-_"(Nat, Nat) [MinusNat]
                | "_*_"(Nat, Nat) [MulNat]
                | "_/_"(Nat, Nat) [DivNat]
    sort Bool ::= builtin Bool | "_==_"(Nat, Nat) | "_<=_"(Nat, Nat) [LeqNat]

    sort Var  ::= builtin String
    sort AExp ::= subsort Nat | subsort Var
    sort AExp ::= "_+_"(AExp, AExp) | "++"(Var)
    sort BExp ::= "_<=_"(AExp, AExp)                [Leq]
    sort Stmt ::= skip
                | "_:=_"(Var, AExp)
                | "if_then_else_"(BExp, Stmt, Stmt) [IteStmt]
                | "while_do_"(BExp, Stmt)           [WhileStmt]
                | "_;_"(Stmt, Stmt)                 [SeqStmt]

    sort Val ::= subsort Nat | subsort Bool | t | f  -- temporary
    sort ValStack ::= nil
                | "_·_"(Val, ValStack)        [consValStack]
    sort Mem ::= empty | "set"(Mem, Var, Val) [memset]
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
abbrev SMCClosedForm := ClosedForm SMC

instance : Coe (SMC.nominal s) (SMCForm s) where
  coe := coeNomSymbs

@[coe]
def Nat.toCtNom (n : ℕ) : SMC.CtNoms SMC.Nat := ⟨toString n, ⟨n, rfl⟩⟩
@[coe]
def Bool.toCtNom (b : Bool) : SMC.CtNoms SMC.Bool := ⟨toString b, by cases b <;> simp⟩
@[coe]
def Bool.toValCtNom : Bool → SMC.CtNoms SMC.Val
  | true  => ⟨SMC.t, rfl⟩
  | false => ⟨SMC.f, rfl⟩

instance : Coe ℕ (SMC.CtNoms SMC.Nat) where
  coe := Nat.toCtNom
instance : Coe Bool (SMC.CtNoms SMC.Bool) where
  coe := Bool.toCtNom
instance : Coe Bool (SMC.CtNoms SMC.Val) where
  coe := Bool.toValCtNom

/-
instance : Coe ℕ (SMCForm SMC.Nat) where
  coe := λ n => ℋNom (.ctNom ⟨toString n, ⟨n, rfl⟩⟩)
instance : Coe Bool (SMCForm SMC.Bool) where
  coe := λ b => ℋNom (.ctNom  b)
instance : Coe Bool (SMCForm SMC.Val) where
  coe := λ b => ℋNom (.ctNom  b)
-/

namespace SMC

@[coe]
abbrev coerceNatAExp (n : SMCForm Nat) : SMCForm AExp := ℋ⟨nat2AExp⟩ n
@[coe]
abbrev coerceVarAExp (v : SMCForm Var) : SMCForm AExp := ℋ⟨var2AExp⟩ v
@[coe]
abbrev coerceNatVal (n : SMCForm Nat) : SMCForm Val := ℋ⟨nat2Val⟩ n
@[coe]
abbrev coerceBoolVal (b : SMCForm Bool) : SMCForm Val := ℋ⟨bool2Val⟩ b


/-
  Subsort operators probably also require some specific axioms
  (to the extent of, e.g., nat2AEXp's accessibility relation
  is an injective function)
-/
instance : Coe (SMCForm Nat) (SMCForm AExp) where
  coe := coerceNatAExp
instance : Coe (SMCForm Nat) (SMCForm Val) where
  coe := coerceNatVal
instance : Coe (SMCForm Var) (SMCForm AExp) where
  coe := coerceVarAExp
instance : Coe (SMCForm Bool) (SMCForm Val) where
  coe := coerceBoolVal

instance : OfNat (SMCForm Nat) n where
  ofNat := n
instance : OfNat (SMCForm AExp) n where
  ofNat := ℋ⟨nat2AExp⟩ n

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
instance : Evaluable (SMCForm Nat) where
  ctrlStackEval := λ x => FormL.appl cAExp x

class HasSeq (α : Type u) where
  seq : α → α → α
instance : HasSeq (SMCForm Stmt) where
  seq := λ s1 s2 => FormL.appl SeqStmt (FormL.cons s1 s2)
instance : HasSeq (SMCForm CtrlStack) where
  seq := λ c1 c2 => FormL.appl PDLSeq (FormL.cons c1 c2)

abbrev plusplus (x : SMCForm Var) := ℋ⟨«++Var_AExp»⟩ x
abbrev asgnStmt (x : SMCForm Var) (a : SMCForm AExp) := ℋ⟨SMC.«_:=_Var_AExp_Stmt»⟩ (x, a)
abbrev union (c1 c2 : SMCForm CtrlStack) := ℋ⟨PDLUnion⟩ (c1, c2)
abbrev aexpPlus (a1 a2 : SMCForm AExp) := ℋ⟨«_+_AExp_AExp_AExp»⟩ (a1, a2)
abbrev aexpLeq (a1 a2 : SMCForm AExp) := ℋ⟨Leq⟩ (a1, a2)
abbrev aexpNat (a1 a2 : SMCForm Nat) := ℋ⟨LeqNat⟩ (a1, a2)
abbrev plusNat (a1 a2 : SMCForm Nat) := ℋ⟨PlusNat⟩ (a1, a2)
abbrev minusNat (a1 a2 : SMCForm Nat) := ℋ⟨MinusNat⟩ (a1, a2)
abbrev mulNat (a1 a2 : SMCForm Nat) := ℋ⟨MulNat⟩ (a1, a2)
abbrev divNat (a1 a2 : SMCForm Nat) := ℋ⟨DivNat⟩ (a1, a2)
abbrev stackCons (v : SMCForm Val) (vs : SMCForm ValStack) := ℋ⟨consValStack⟩ (v, vs)
abbrev star (c1 : SMCForm CtrlStack) := ℋ⟨PDLStar⟩ (c1)
abbrev test (v : SMCForm Val) := ℋ⟨PDLTest⟩ v
/-- Note!: [α] φ = ¬ ⟨α⟩ ¬ φ -/
abbrev pdlOp (ctrl : SMCForm CtrlStack) (config : SMCForm Config) := ℋ⟨PDLOp⟩ᵈ (∼ctrl, config)
abbrev config (vs : SMCForm ValStack) (mem : SMCForm Mem) := ℋ⟨mkConfig⟩ (vs, mem)
def asgn (x : SMCForm Var) := ℋ⟨SMC.asgnVar_CtrlStack⟩ x
def ifthenelse (bexp : SMCForm BExp) (s1 s2 : SMCForm Stmt) := ℋ⟨IteStmt⟩ (bexp, s1, s2)
def whiledo (bexp : SMCForm BExp) (s : SMCForm Stmt) := ℋ⟨WhileStmt⟩ (bexp, s)
def set (mem : SMCForm Mem) (x : SMCForm Var) (n : SMCForm Val) := ℋ⟨memset⟩ (mem, x, n)

prefix:102 "++" => plusplus
infix:100 " ::= " => asgnStmt
infix:100 " ∪ "   => union
infixr:102 " + "  => aexpPlus
infix:100 " <= "  => aexpLeq
infix:100 " <= "  => aexpNat
infixr:100 " +Nat " => plusNat
infixl:100 " -Nat " => minusNat
infixr:100 " *Nat " => mulNat
infixl:100 " /Nat " => divNat
infixr:100 " ⬝ "   => stackCons
postfix:100 "*"   => star
postfix:100 "?"   => test

notation:100 s1:99 "; " s2:100 => HasSeq.seq s1 s2
notation:100 "[" ctrl "]" config => pdlOp ctrl config
notation:100 "c" "(" φ:100 ")" => Evaluable.ctrlStackEval φ
notation:100 "⟨" vs ", " mem "⟩" => config vs mem
notation:100 "asgn" "(" x ")" => asgn x
notation:100 "if " bexp " then " s1 " else " s2 "endif" => ifthenelse bexp s1 s2
notation:100 "while " bexp " do: " s " od" => whiledo bexp s
notation:100 "set" "(" mem ", "  x ", "  n ")" => set mem x n

open Lean PrettyPrinter

@[app_unexpander pdlOp]
def unexpandPdlOp : Unexpander
  | `($_ $ctrl $config) => `([$ctrl] $config)
  | _ => throw ()
@[app_unexpander config]
def unexpandConfig : Unexpander
  | `($_ $vs $mem) => `(⟨$vs, $mem⟩)
  | _ => throw ()
/-
@[app_unexpander FormL.appl]
def unexpandConfig' : Unexpander
  | `($_ ``mkConfig $vs $mem) => `(⟨$vs, $mem⟩)
  | _ => throw ()
-/
@[app_unexpander ifthenelse]
def unexpandIte : Unexpander
  | `($_ $bexp $s1 $s2) =>
        `(if ($bexp) then $s1 else $s2 )
  | _ => throw ()
@[app_unexpander whiledo]
def unexpandWhile : Unexpander
  | `($_ $bexp $s) =>
        `(while ($bexp) do: $s od )
  | _ => throw ()

end SMC
