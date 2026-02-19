import Hybrid.Examples.SMC.Axioms
import Hybrid.Proof

open SMC

namespace Proof

section Axioms

def aseqL : SMCProof _
  (([π ; π'] γ) ⟶ [π][π'] γ) := -- FIXME: binding of implications!
  .mp .conj_elimL_proof (.ax ⟨_, .intro .ASeq⟩)

def aseqR : SMCProof _
  (([π][π'] γ) ⟶ [π ; π'] γ) := -- FIXME: binding of implications!
  .mp .conj_elimR_proof (.ax ⟨_, .intro .ASeq⟩)

def aint {n : SMCForm Nat} : SMCProof _
  (⟨vs, mem⟩ ⟶ [c(n)] ⟨n ⬝ vs, mem⟩) := .ax ⟨_, .intro .Aint⟩

def aasgn : SMCProof _
  (⟨n ⬝ vs, mem⟩ ⟶ [asgn(x)] ⟨vs, set(mem, x, n)⟩) := .ax ⟨_, .intro .AAsgn⟩

def aid : SMCProof _
  (⟨vs, set(mem, x, n)⟩ ⟶ [c(x)] ⟨n ⬝ vs, set(mem, x, n)⟩) := .ax ⟨_, .intro .Aid⟩

def dasgn : SMCProof _
      (c(x ::= a) ←→ c(a) ; asgn(x)) := .ax ⟨_, .intro .DAsgn⟩

def amem1 (h : x ≠ y) : SMCProof _
  (set(set(mem, x, n), y, m) ←→ set(set(mem, y, m), x, n)) := .ax ⟨_, .intro <| .AMem1 h⟩

def atesttrue : SMCProof _
  (ℋ@ v' v ⋀ ⟨v ⬝ vs, mem⟩ ⟶ [v' ?] ⟨vs, mem⟩ ⋀ ℋ@ v' v) := .ax ⟨_, .intro .ATestTrue⟩

def atestfalse : SMCProof _
  (ℋ@ v' (∼v) ⋀ ⟨v ⬝ vs, mem⟩ ⟶ [v' ?] ψ) := .ax ⟨_, .intro .ATestFalse⟩

def app {n : SMCForm Nat} : SMCProof _
  (⟨vs, set(mem, x, n)⟩ ⟶ [c(++x)] ⟨(n +Nat 1) ⬝ vs, set(mem, x, (n +Nat 1))⟩) := .ax ⟨_, .intro .App⟩

def dwhile {bexp : SMCForm BExp} : SMCProof _
  (c(while bexp do: s od) ←→ c(bexp) ; (true ? ; c(s) ; c(bexp))* ; false ?) := .ax ⟨_, .intro .DWhile⟩

def dleq {a1 a2 : SMCForm AExp} : SMCProof _
  (c(a1 <= a2) ←→ c(a1) ; c(a2) ; leq) := .ax ⟨_, .intro .DLeq⟩

def aleq  (n1 n2 : SMCForm Nat)
          (vs : SMCForm ValStack)
          (mem : SMCForm Mem): SMCProof _
  (⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [leq] ⟨(n1 <=Nat n2) ⬝ vs, mem⟩) :=  .ax ⟨_, .intro .ALeq⟩

def dplus : SMCProof _
  (c(a1 + a2) ←→ c(a1) ; c(a2) ; plus) := .ax ⟨_, .intro .DPlus⟩

def bubble3Mem (neq1 : x ≠ y) (neq2 : x ≠ z) :
  SMCProof _
    (set(set(set(mem, x, vx), y, vy), z, vz) ←→ set(set(set(mem, y, vy), z, vz), x, vx)) :=
      Proof.ax ⟨_, Nonempty.intro (.ABubble3Mem neq1 neq2)⟩

def nleq {n1 n2 : ℕ}: SMCProof _
  ((n1 <=Nat n2) ←→ n1.ble n2) := .ax ⟨_, .intro .NLeq⟩

end Axioms

section Propagation

def propagateNLeq {n1 n2 : ℕ} (h : n1.ble n2):
    SMCProof _ (n1 <=Nat n2) := by
  have l1 : SMCProof Bool ((n1 <=Nat n2) ←→ n1.ble n2) := nleq
  rw [h] at l1
  apply mp (mp conj_elimR_proof l1)
  exact ax ⟨_, .intro .ATrue⟩

def propagateSeq {s1 s2 : SMCForm Stmt}
    (h : SMCProof _ (φ ⟶ [c(s1) ; c(s2)] cfg)) :
  SMCProof _ (φ ⟶ [c(s1 ; s2)] cfg) := by
  have propagateNeg : SMCProof _ ((∼c(s1 ; s2)) ←→ ∼(c(s1); c(s2))) := simpNeg <| .ax ⟨_, .intro .CStmtAx⟩
  have propagateSigma := @simpDualAppl
            String _ SMC CtrlStack
            _ _ _
            propagateNeg
            _ _
            (∼(c(s1 ; s2)), cfg)
            _
            PDLOp .head
  have propagateImplL : SMCProof _ ((φ ⟶ _) ←→ (φ ⟶ _)) := simpImplL propagateSigma
  apply mp _ h
  apply mp conj_elimR_proof
  exact propagateImplL

def propagateDAsgn {v : SMCForm AExp} (h : SMCProof _ (φ ⟶ [c(v); asgn(s)] cfg)) :
    SMCProof _ (φ ⟶ [c(s ::= v)] cfg) := by
  have propagateNeg : SMCProof _ ((∼c(s ::= v)) ←→ ∼(c(v); asgn(s))) := simpNeg dasgn
  have propagateSigma := @simpDualAppl
            String _ SMC CtrlStack
            _ _ _
            propagateNeg
            _ _
            (∼(c(s ::= v)), cfg)
            _
            PDLOp .head
  have propagateImplL : SMCProof _ ((φ ⟶ _) ←→ (φ ⟶ _)) := simpImplL propagateSigma
  apply mp _ h
  apply mp conj_elimR_proof
  exact propagateImplL

def propagateDIf {bexp : SMCForm BExp}
    (h : SMCProof _ (φ ⟶ [c(bexp) ; ((true : CtNoms Val) ? ; c(s1)) ∪ ((false : CtNoms Val) ? ; c(s2))] ψ)) :
  SMCProof _ (φ ⟶ [c(if bexp then s1 else s2 endif)] ψ) := by
  let ctrlStack := c(bexp) ; ((true : CtNoms Val) ? ; c(s1)) ∪ ((false : CtNoms Val) ? ; c(s2))
  have C : (∼(ctrlStack)).Context (∼(ctrlStack), ψ) := .head
  have propagateNeg : SMCProof _ ((∼ctrlStack) ←→ ∼(c(if bexp then s1 else s2 endif))) := simpNeg <| .ax ⟨_, .intro .DIf⟩
  have propagateSigma := @simpDualAppl
            String _ SMC CtrlStack
            _ _ _
            propagateNeg
            _ _
            (∼(ctrlStack), ψ)
            _
            PDLOp .head
  have propagateImplL : SMCProof _ ((φ ⟶ _) ←→ (φ ⟶ _)) := simpImplL propagateSigma
  apply mp _ h
  apply mp conj_elimL_proof
  exact propagateImplL

def propagateDLeq {a1 a2 : SMCForm AExp}
  (h : SMCProof _ (φ ⟶ [c(a1) ; c(a2) ; leq] ψ)):
  SMCProof _ (φ ⟶ [c(a1 <= a2)] ψ) := by
  let ctrlStack := c(a1) ; c(a2) ; leq
  have C : (∼(ctrlStack)).Context (∼(ctrlStack), ψ) := .head
  have propagateNeg : SMCProof _ ((∼(c(a1 <= a2)) ←→ (∼(c(a1) ; c(a2) ; leq)))) := simpNeg dleq
  have propagateSigma := @simpDualAppl
            String _ SMC CtrlStack
            _ _ _
            propagateNeg
            _ _
            (∼(c(a1 <= a2)), ψ)
            _
            PDLOp .head
  have propagateImplL : SMCProof _ ((φ ⟶ _) ←→ (φ ⟶ _)) := simpImplL propagateSigma
  apply mp _ h
  apply mp conj_elimR_proof
  exact propagateImplL

def propagateMemL {mem1 mem2 : SMCForm Mem}
    (h1 : SMCProof _ (mem1 ←→ mem2))
    (h2 : SMCProof _ (⟨vs, mem2⟩ ⟶ [pgm] cfg)) : SMCProof _ (⟨vs, mem1⟩ ⟶ [pgm] cfg) := by
  apply imp_trans_proof _ h2
  apply mp conj_elimL_proof (simpAppl _ (.tail .refl))
  exact h1

def propagateStackL {vs1 vs2 : SMCForm ValStack}
    (h1 : SMCProof _ (vs1 ←→ vs2))
    (h2 : SMCProof _ (⟨vs2, mem⟩ ⟶ [pgm] cfg)) : SMCProof _ (⟨vs1, mem⟩ ⟶ [pgm] cfg) := by
  apply imp_trans_proof _ h2
  apply mp conj_elimL_proof (simpAppl _ .head)
  exact h1

def propagateStackL' {vs1 vs2 : SMCForm ValStack}
    (h1 : SMCProof _ (vs1 ⟶ vs2))
    (h2 : SMCProof _ (⟨vs2, mem⟩ ⟶ [pgm] cfg)) : SMCProof _ (⟨vs1, mem⟩ ⟶ [pgm] cfg) := by
  apply imp_trans_proof _ h2
  let C : (vs1).Context (vs1, mem) := .head
  have : (vs2, mem) = C[vs2] := rfl
  simp [config, this]
  apply impAppl
  exact h1

def propagateMemR {mem1 mem2 : SMCForm Mem}
    (h1 : SMCProof _ (mem1 ←→ mem2))
    (h2 : SMCProof _ (cfg ⟶ [pgm] ⟨vs, mem2⟩)) : SMCProof _ (cfg ⟶ [pgm] ⟨vs, mem1⟩) := by
  apply imp_trans_proof h2
  let C : (⟨vs, mem2⟩ ⟶ ⟨vs, mem1⟩).Context (∼pgm, ⟨vs, mem2⟩ ⟶ ⟨vs, mem1⟩) := .tail .refl
  have : (∼pgm, ⟨vs, mem1⟩) = C[⟨vs, mem1⟩] := rfl
  simp [pdlOp, this]
  have : (∼pgm, ⟨vs, mem2⟩) = C[⟨vs, mem2⟩] := rfl
  simp [this]
  apply mp (k _ _ _ _ C)
  apply ug (.tail .refl)
  let C' : mem2.Context (vs, mem2) := .tail .refl
  have : (vs, mem1) = C'[mem1] := rfl
  simp [config, this]
  apply impAppl C'
  exact mp conj_elimR_proof h1

def propagateACup
    (h1 : SMCProof _ (φ ⟶  [π] γ))
    (h2 : SMCProof _ (φ ⟶ [π'] γ)) :
      SMCProof _ (φ ⟶ [π ∪ π'] γ) := by
  let l1 : SMCProof _ ((([π] γ) ⋀ [π'] γ) ⟶ [π ∪ π'] γ) := mp conj_elimL_proof (ax ⟨_, .intro .ACup⟩)
  apply imp_trans_proof _ l1
  apply conj_intro_hyp
  repeat assumption

def propagateDAdd {n m : ℕ} :
  SMCProof _ (⟨(n + m) ⬝ vs, mem⟩ ⟶ [α] φ)
  → SMCProof _ (⟨(n +Nat m) ⬝ vs, mem⟩ ⟶ [α] φ) := by
  apply propagateStackL'
  let C : ((n +Nat m):SMCForm Val).Context (((n +Nat m):SMCForm Val), vs) := .head
  let add : SMCForm Val := n+m
  have : (add, vs) = C[add] := rfl
  simp [add] at this
  simp [stackCons, this]
  apply impAppl
  apply mp conj_elimL_proof
  exact .ax ⟨_, .intro .APlusNat⟩

end Propagation

section Lemmas

def kPgm :
  SMCProof _ (([α] φ ⟶ ψ) ⟶ ([α] φ) ⟶ ([α] ψ)) :=
   k _ _ _ _ (.tail .refl)

def necessPgm :
  SMCProof _ φ → SMCProof _ ([α] φ) :=
    ug (.tail .refl)

def atInv :
  SMCProof _ (ℋ@ i φ ⟶ [α] ℋ@ i φ) :=
    backContrapositive (.tail .refl)

def falseNatLeq {n m : ℕ} (h : n.ble m) :
  SMCProof s (ℋ@ false ((n <=Nat m):SMCForm Val) ⟶ ℋ⊥) := by
  apply imp_trans_proof
  . exact mp conj_elimR_proof (ax ⟨_, .intro .AFalseValEmbed⟩)
  . apply imp_trans_proof
    . apply mp conj_elimL_proof
      exact ax ⟨_, .intro .AFalse⟩
    . apply mp dni'
      apply genAt
      exact propagateNLeq h

end Lemmas

section Rules

-- Following two rules are grouped together as
--   "Rule of Consequence" in the paper:

def strengtheningPre
    (h1 : SMCProof _ (φ ⟶ [α] ψ))
    (h2 : SMCProof _ (χ ⟶ φ)) :
  SMCProof _ (χ ⟶ [α] ψ) := by
    exact imp_trans_proof h2 h1

def weakeningPost
    (h1 : SMCProof _ (φ ⟶ [α] ψ))
    (h2 : SMCProof _ (ψ ⟶ χ)) :
  SMCProof _ (φ ⟶ [α] χ) := by
    let ctx : (ψ ⟶ χ).Context (∼α, ψ ⟶ χ) := .tail .refl
    have l1 : SMCProof _ ([α] (ψ ⟶ χ)) := .ug ctx h2
    have l2 : SMCProof _ (([α] (ψ ⟶ χ)) ⟶ ([α] ψ) ⟶ [α] χ) :=
        .k _ _ (∼α, ψ ⟶ χ) _ ctx
    have l3 := Proof.mp l2 l1
    exact imp_trans_proof h1 l3

def composition
    (h1 : SMCProof _ (φ₀ ⟶ [α₁] φ₁))
    (h2 : SMCProof _ (φ₁ ⟶ [α₂] φ₂)) :
  SMCProof _ (φ₀ ⟶ [α₁ ; α₂] φ₂) := by
  have l1 : SMCProof _ ([α₁] (φ₁ ⟶ [α₂] φ₂)) := ug (.tail .refl) h2
  -- Some ugly technicalities:
  --   Reasoning with contexts forces us to break the nice [α] φ notation into
  --   primitive applications of ℋ⟨PDLOp⟩ᵈ
  let C : (φ₁ ⟶ [α₂] φ₂).Context (∼α₁, (φ₁ ⟶ [α₂] φ₂)) := .tail .refl
  have l2 : SMCProof _ (ℋ⟨PDLOp⟩ᵈ (∼α₁, φ₁ ⟶ [α₂] φ₂) ⟶ (ℋ⟨PDLOp⟩ᵈ C[φ₁]) ⟶ ℋ⟨PDLOp⟩ᵈ C[ℋ⟨PDLOp⟩ᵈ (∼α₂, φ₂)]) := k _ _ _ _ C
  --
  have l3 : SMCProof _ (([α₁] φ₁) ⟶ [α₁][α₂] φ₂) := mp l2 l1
  have l4 : SMCProof _ (φ₀ ⟶ [α₁][α₂] φ₂) := imp_trans_proof h1 l3
  have l5 := imp_trans_proof l4 aseqR
  exact l5

def assignment (s : SMCForm Var) (x : SMCForm Var):
  SMCProof _  (⟨vs, mem⟩ ⟶ [c(x)] ⟨v ⬝ vs, mem⟩) →
  SMCProof _  (⟨vs, mem⟩ ⟶ [c(s ::= x)] ⟨vs, set(mem, s, v)⟩) := by
  intro h
  apply propagateDAsgn
  apply composition h
  apply aasgn

def conditional {b : SMCForm BExp}
    (h1 : SMCProof _ (φ ⟶ [c(b)] ⟨B ⬝ vs, mem⟩))
    (h2 : SMCProof _ (⟨vs, mem⟩ ⋀ ℋ@ true B ⟶ [c(s₁)] χ))
    (h3 : SMCProof _ (⟨vs, mem⟩ ⋀ ℋ@ false B ⟶ [c(s₂)] χ)):
  SMCProof _ (φ ⟶ [c(if b then s₁ else s₂ endif)] χ) := by
  apply propagateDIf
  . apply composition
    . exact h1
    . apply propagateACup
      . apply composition
        case h.h2.h1.h2 =>
          exact h2
        . let tr : SMC.nominal Val := true
          apply
            Proof.mp
              (Proof.mp
                (Proof.mp disj_elim_proof $ tertium_non_daturAt_proof tr B)
                _)
          . apply export_proof
            apply atestfalse
          . apply export_proof
            apply atesttrue
      . apply composition
        case h.h2.h2.h2 =>
          exact h3
        . let fl : SMC.nominal Val := Symbols.nominal.ctNom ↑false
          apply
            Proof.mp
              (Proof.mp
                (Proof.mp disj_elim_proof $ tertium_non_daturAt_proof fl B)
                _)
          . apply export_proof
            apply atestfalse
          . apply export_proof
            apply atesttrue

end Rules
