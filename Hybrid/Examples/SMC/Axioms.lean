import Hybrid.Examples.SMC.Signature
import Hybrid.Proof.Hilbert
import Hybrid.Proof.Proofs

namespace SMC

-- c(s1 ; s2) ↔ c(s1) ; c(s2)
def CStmtAx (s1 s2 : SMCForm Stmt)
  : SMCForm CtrlStack :=
    c(s1 ; s2) ←→ c(s1) ; c(s2)

-- ⟨vs, mem⟩ → [c(n)] ⟨n ⬝ vs, mem⟩, where n is an integer
def Aint (vs : SMCForm ValStack)
         (mem : SMCForm Mem)
         (n : SMCForm Nat)
    : SMCForm Config :=
    ⟨vs, mem⟩ ⟶ [c(n)] ⟨n ⬝ vs, mem⟩

-- ⟨vs, set(mem, x, n)⟩ → [c(x)] ⟨n ⬝ vs, set(mem, x, n)⟩
abbrev Aid (vs : SMCForm ValStack)
        (mem : SMCForm Mem)
        (x : SMCForm Var)
        (n : SMCForm Val)
    : SMCForm Config :=
    ⟨vs, set(mem, x, n)⟩ ⟶ [c(x)] ⟨n ⬝ vs, set(mem, x, n)⟩

-- ⟨vs, set(mem, x, n)⟩ → [c(++x)] ⟨(n+1) ⬝ vs, set(mem, x, n+1)⟩
def App  (vs : SMCForm ValStack)
         (mem : SMCForm Mem)
         (x : SMCForm Var)
         (n : SMCForm Nat)
  : SMCForm Config :=
    ⟨vs, set(mem, x, n)⟩ ⟶ [c(++x)] ⟨(n +Nat 1) ⬝ vs, set(mem, x, (n +Nat 1))⟩

-- c(a1 + a2) ↔ c(a1) ; c(a2) ; plus
def DPlus (a1 a2 : SMCForm AExp) : SMCForm CtrlStack :=
    c(a1 + a2) ←→ c(a1) ; c(a2) ; plus

-- ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [plus] ⟨n1 + n2 ⬝ vs, mem⟩
def Aplus (n1 n2 : SMCForm Nat)
          (vs : SMCForm ValStack)
          (mem : SMCForm Mem)
    : SMCForm Config :=
      ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [plus] ⟨(n1 +Nat n2) ⬝ vs, mem⟩

-- c(a1 <= a2) ↔ c(a1) ; c(a2) ; leq
def DLeq (a1 a2 : SMCForm AExp) : SMCForm CtrlStack :=
    c(a1 <= a2) ←→ c(a1) ; c(a2) ; leq

-- ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [leq] ⟨↑(n1 ≤ n2), mem⟩
def ALeq (n1 n2 : SMCForm Nat)
          (vs : SMCForm ValStack)
          (mem : SMCForm Mem)
    : SMCForm Config :=
      ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [leq] ⟨(n1 <=Nat n2) ⬝ vs, mem⟩

-- γ ⟶ [skip] γ
def ASkip (γ : SMCForm Config): SMCForm Config :=
      γ ⟶ [c(skip)] γ

-- DAsgn c(x := a) ↔ c(a) ; asgn(x)
def DAsgn (x : SMCForm Var)
          (a : SMCForm AExp) : SMCForm CtrlStack :=
      c(x ::= a) ←→ c(a) ; asgn(x)

-- AAsgn ⟨n ⬝ vs, mem) ⟶ [asgn(x)] ⟨vs, set(mem, x, n)⟩
def AAsgn (n : SMCForm Val)
          (vs : SMCForm ValStack)
          (mem : SMCForm Mem)
          (x : SMCForm Var): SMCForm Config :=
      ⟨n ⬝ vs, mem⟩ ⟶ [asgn(x)] ⟨vs, set(mem, x, n)⟩

-- DIf
--   c(if bexp then s1 else s2) ↔ c(bexp) ; ( (true? ; c(s1)) ∪ (false? ; c(s2)) )
def DIf (bexp : SMCForm BExp)
          (s1 s2 : SMCForm Stmt) : SMCForm CtrlStack :=
      c(bexp) ; ((true : CtNoms Val) ? ; c(s1)) ∪ ((false : CtNoms Val) ? ; c(s2)) ←→ c(if bexp then s1 else s2 endif)

-- Memory consistency axioms:

def AMem1 (x y : SMCForm Var)
          (h : x ≠ y)
          (n m : SMCForm Val)
          (mem : SMCForm Mem) : SMCForm Mem :=
        set(set(mem, x, n), y, m) ←→ set(set(mem, y, m), x, n)

def AMem2 (x : SMCForm Var)
          (n m : SMCForm Val)
          (mem : SMCForm Mem) : SMCForm Mem :=
        set(set(mem, x, n), x, m) ←→ set(mem, x, m)

-- PDL-inspired axioms:
def ACup (π π' : SMCForm CtrlStack)
         (γ : SMCForm Config) : SMCForm Config :=
        (([π] γ) ⋀ [π'] γ) ←→ [π ∪ π'] γ

def ASeq (π π' : SMCForm CtrlStack)
         (γ : SMCForm Config) : SMCForm Config :=
        ([π ; π'] γ) ←→ [π][π'] γ  -- FIXME: binding of implications / equivs

def ATestTrue (v : SMCForm Val)
         (v' : SMC.nominal Val)
         (vs : SMCForm ValStack)
         (mem : SMCForm Mem) : SMCForm Config :=
        ℋ@ v' v ⋀ ⟨v ⬝ vs, mem⟩ ⟶ [v' ?] ⟨vs, mem⟩ ⋀ ℋ@ v' v

def ATestFalse (v : SMCForm Val)
         (v' : SMC.nominal Val)
         (vs : SMCForm ValStack)
         (mem : SMCForm Mem)
         (ψ : SMCForm Config) : SMCForm Config :=
        ℋ@ v' (∼v) ⋀ ⟨v ⬝ vs, mem⟩ ⟶ [v' ?] ψ


-- DWhile
--   c(while bexp do s) ↔ c(bexp) ; ( (true?) ; c(s) ; c(bexp) )* ; false?
def DWhile (bexp : SMCForm BExp)
          (s : SMCForm Stmt) : SMCForm CtrlStack :=
    c(while bexp do: s od) ←→ c(bexp) ; (true ? ; c(s) ; c(bexp))* ; false ?

def AStar (π : SMCForm CtrlStack)
         (γ : SMCForm Config) : SMCForm Config :=
        [π*] γ ←→ γ ⋀ [π][π*] γ

def AInd (π : SMCForm CtrlStack)
         (γ : SMCForm Config) : SMCForm Config :=
        γ ⋀ [π*](γ ⟶ [π]γ) ←→ [π*] γ

-- Subsorting axioms!
-- Bool < Val:
def ATrueBoolVal : SMCForm Val :=
        true ←→ ℋ⟨bool2Val⟩(true)
def AFalseBoolVal : SMCForm Val :=
        false ←→ ℋ⟨bool2Val⟩(false)
def ATrueValEmbed {φ : SMCForm Bool} : SMCForm s :=
        ℋ@ true φ ←→ ℋ@ true (ℋ⟨bool2Val⟩ φ)
def AFalseValEmbed {φ : SMCForm Bool} : SMCForm s :=
        ℋ@ false φ ←→ ℋ@ false (ℋ⟨bool2Val⟩ φ)

inductive Axiom : {s : Sorts} → SMCForm s → Type
  | CStmtAx {s1 s2}     : Axiom (CStmtAx s1 s2)
  | Aint {vs mem n}     : Axiom (Aint vs mem n)
  | Aid {vs mem x n}    : Axiom (Aid vs mem x n)
  | App {vs mem x n}    : Axiom (App vs mem x n)
  | DLeq {a1 a2}        : Axiom (DLeq a1 a2)
  | ALeq {n1 n2 vs mem} : Axiom (ALeq n1 n2 vs mem)
  | ASkip {γ}           : Axiom (ASkip γ)
  | DAsgn {x a}         : Axiom (DAsgn x a)
  | AAsgn {n vs mem x}  : Axiom (AAsgn n vs mem x)
  | DIf {bexp s1 s2}    : Axiom (DIf bexp s1 s2)
  | DWhile {bexp s}     : Axiom (DWhile bexp s)
  | ACup {π π' γ}       : Axiom (ACup π π' γ)
  | ASeq {π π' γ}       : Axiom (ASeq π π' γ)
  | ATestTrue {v v' vs mem} : Axiom (ATestTrue v v' vs mem)
  | ATestFalse {v v' vs mem ψ}: Axiom (ATestFalse v v' vs mem ψ)
  | AStar {π γ}         : Axiom (AStar π γ)
  | AInd {π γ}          : Axiom (AInd π γ)
  | ATrueBoolVal        : Axiom (ATrueBoolVal)
  | AFalseBoolVal       : Axiom (AFalseBoolVal)
  | ATrueValEmbed       : Axiom (ATrueValEmbed)
  | AFalseValEmbed      : Axiom (AFalseValEmbed)
  | AFalse {φ : SMCForm Bool}     : Axiom (ℋ@ false φ ←→ ∼ℋ@ true φ)
  | NLeq {n1 n2 : ℕ}    : Axiom ((n1 <=Nat n2) ←→ n1.ble n2)
  | APlusNat {n₁ n₂ : ℕ}: Axiom (((n₁ +Nat n₂):SMCForm Val) ←→ (n₁ + n₂))                -- move me
  -- Helper axioms for memory reasoning:
  | AMem1 {x y n m mem} h : Axiom (AMem1 x y h n m mem)
  | ABubble3Mem (neq1 : x ≠ y) (neq2 : x ≠ z) :
        Axiom ((set(set(set(mem, x, vx), y, vy), z, vz) ←→ set(set(set(mem, y, vy), z, vz), x, vx)))
  | AStackLike3 (neq1 : y ≠ x) (neq2 : y ≠ z) (neq3 : x ≠ z):
        Axiom ((set(set(set(set(mem, x, xn), y, zn), z, zn), y, xn) ←→ set(set(set(mem, x, xn), y, xn), z, zn)))
  | AStackLike4 (neq1 : x ≠ z) (neq2 : x ≠ y) (neq3 : z ≠ y):
        Axiom (set(set(set(mem, x, xn), y, yn), z, zn) ←→ set(set(set(set(mem, z, zn'), x, xn), y, yn), z, zn))
  | AMemStack {n m : ℕ} (neq : x ≠ y) :
        Axiom (⟨vs, set(set(set(mem, x, (n +Nat m)), y, yn), z, zn)⟩ ⟶ ⟨vs, set(set(mem, x, (n+m)), z, zn)⟩)

-- The set of axioms for SMC is that of formulas φ for which a term
-- Axiom φ exists, for all s s:
@[simp] def SMCΛ : AxiomSet SMC := λ s => { φ | Nonempty (Axiom φ) }

-- The Hilbert proof system for SMC:
def SMCProof := Proof SMCΛ

end SMC
