import Hybrid.Examples.SMC.Axioms
import Hybrid.Proof.Equiv.Equiv

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

def app {n : ℕ} : SMCProof _
  (⟨vs, set(mem, x, n)⟩ ⟶ [c(++x)] ⟨↑(n.add 1) ⬝ vs, set(mem, x, ↑(n.add 1))⟩) := .ax ⟨_, .intro .App⟩

def dwhile {bexp : SMCForm BExp} : SMCProof _
  (c(while bexp do: s od) ←→ c(bexp) ; (true ? ; c(s) ; c(bexp))* ; false ?) := .ax ⟨_, .intro .DWhile⟩

def dleq {a1 a2 : SMCForm AExp} : SMCProof _
  (c(a1 <= a2) ←→ c(a1) ; c(a2) ; leq) := .ax ⟨_, .intro .DLeq⟩

def aind : SMCProof _
  (γ ⋀ [π*](γ ⟶ [π]γ) ←→ [π*] γ) := .ax ⟨_, .intro .AInd⟩

end Axioms

section Propagation

def propagateSeq {s1 s2 : SMCForm Stmt} (h : SMCProof _ (φ ⟶ [c(s1) ; c(s2)] cfg)) : SMCProof _ (φ ⟶ [c(s1 ; s2)] cfg) := by sorry

def assgnVar (s : SMCForm Var) (x : SMCForm Var):
  SMCProof _  (⟨vs, mem⟩ ⟶ [c(x)] ⟨v ⬝ vs, mem⟩) →
  SMCProof _  (⟨vs, mem⟩ ⟶ [c(s ::= x)] ⟨vs, set(mem, s, v)⟩) := by
    admit

def bubble3Mem (neq1 : x ≠ y) (neq2 : x ≠ z) :
  SMCProof _
    (set(set(set(mem, x, vx), y, vy), z, vz) ←→ set(set(set(mem, y, vy), z, vz), x, vx)) := sorry

def propagateMemL {mem1 mem2 : SMCForm Mem}
  (h1 : SMCProof _ (mem1 ←→ mem2))
  (h2 : SMCProof _ (⟨vs, mem2⟩ ⟶ [pgm] cfg)) : SMCProof _ (⟨vs, mem1⟩ ⟶ [pgm] cfg) := by sorry

def propagateMemR {mem1 mem2 : SMCForm Mem}
  (h1 : SMCProof _ (mem1 ←→ mem2))
  (h2 : SMCProof _ (cfg ⟶ [pgm] ⟨vs, mem2⟩)) : SMCProof _ (cfg ⟶ [pgm] ⟨vs, mem1⟩) := by sorry

def propagateDAsgn {v : SMCForm Nat} (h : SMCProof _ (φ ⟶ [c(v); asgn(s)] cfg)) : SMCProof _ (φ ⟶ [c(s ::= v)] cfg) := by
  simp [Evaluable.ctrlStackEval] at h ⊢
  have C : (∼(c(v); asgn(s))).Context (∼(c(v); asgn(s)), cfg) := .head
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
  SMCProof _ (φ ⟶ [c(if bexp then s1 else s2 endif)] ψ) := sorry

def propagateACup
    (h1 : SMCProof _ (φ ⟶  [π] γ))
    (h2 : SMCProof _ (φ ⟶ [π'] γ)) :
  SMCProof _ (φ ⟶ [π ∪ π'] γ) := sorry

def propagateDWhile {bexp : SMCForm BExp}
    (h : SMCProof _ (φ ⟶ [c(bexp) ; ((true : CtNoms Val) ? ; c(s) ; c(bexp))* ; (false : CtNoms Val) ?] γ)):
  SMCProof _ (φ ⟶ [c(while bexp do: s od)] γ) := sorry

def propagateDLeq {a1 a2 : SMCForm AExp}
  (h : SMCProof _ (φ ⟶ [c(a1) ; c(a2) ; leq] ψ)):
  SMCProof _ (φ ⟶ [c(a1 <= a2)] ψ) := sorry

def propagateAInd
    (h : SMCProof _ (φ ⟶ γ ⋀ [π*](γ ⟶ [π]γ))):
  SMCProof _ (φ ⟶ [π*] γ) := sorry

end Propagation

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

def helperDistributeEx :
  SMCProof _ ((φ ⟶ ψ).existClosure vars) →
  SMCProof _ (φ.existClosure vars ⟶ ψ) := sorry

def iteration {b : SMCForm BExp} {s : SMCForm Stmt}
    (cl₁ : b.closed) (cl₂: s.closed)
    (B : SMCForm Val) (vs : SMCForm ValStack) (mem : SMCForm Mem)
    (init : ⟨B ⬝ vs, mem⟩.Instance)
    (h1 : SMCProof _ (φ ⟶ [c(b)] init.form))
    (h2 : (preBody : (⟨vs, mem⟩ ⋀ ℋ@ (true : SMC.CtNoms Val) B).Instance) → Σ (body : ⟨B ⬝ vs, mem⟩.Instance),
      SMCProof _ (preBody.form ⟶ [c(s) ; c(b)] body.form)):
  (SMCProof _ (φ ⟶ [c(while b do: s od)] (⟨vs, mem⟩ ⋀ ℋ@ (false : SMC.nominal Val) B).existClosure (⟨B ⬝ vs, mem⟩).FV)) := by
  apply propagateDWhile
  . apply composition
    . exact h1
    . apply composition
      case h.h2.φ₁ =>
        exact (⟨B ⬝ vs, mem⟩).existClosure (⟨B ⬝ vs, mem⟩).FV
      . apply propagateAInd
        apply helperInsertAnd
        . apply instanceToExistPf
        . apply Proof.mp (.prop1 _ _)
          apply Proof.ug (.tail .refl)
          apply Proof.mp (existElimPf _)
          . apply instanceToUnivPf' init
            . admit
            . simp only [FormL.Instance.distribAppl, FormL.Instance.distribCons]
              let Binit   := init.inst.apply B
              let vsinit  := init.inst.apply vs
              let meminit := init.inst.apply mem
              rw [show (init.inst.apply B = Binit) by rfl, show (init.inst.apply vs = vsinit) by rfl, show (init.inst.apply mem = meminit) by rfl]
              let tr : SMC.nominal Val := true
              apply
                Proof.mp
                  (Proof.mp
                    (Proof.mp disj_elim_proof $ tertium_non_daturAt_proof tr Binit)
                    _)
              . apply export_proof
                apply composition
                . apply atestfalse
                . apply id_proof
              . apply export_proof
                apply composition
                . apply atesttrue
                . obtain ⟨body, pf⟩ := h2 ⟨init.inst⟩
                  simp [FormL.Instance.form] at pf
                  apply imp_trans_proof pf
                  . let preBody := ⟨(body.inst.apply B ⬝ body.inst.apply vs), body.inst.apply mem⟩
                    let preBodyFVs := ⟨(B ⬝ vs), mem⟩
                    let preBodyExists := preBodyFVs.existClosure preBodyFVs.FV
                    let pgm := ∼c(s) ; c(b)
                    let C : (preBody ⟶ preBodyExists).Context (pgm, (preBody ⟶ preBodyExists)) := .tail .refl
                    apply Proof.mp (Proof.k preBody preBodyExists _ PDLOp C)
                    apply Proof.ug C
                    let preBodyInst : preBodyFVs.Instance := ⟨body.inst⟩
                    rw [ show (preBody = preBodyInst.form) by simp [preBody, preBodyFVs, preBodyInst] ]
                    apply instanceToExistPf
          . admit
      . apply Proof.mp (existElimPf _)
        . apply genIterated
          let fl : SMC.nominal Val := false
          apply
            Proof.mp
              (Proof.mp
                (Proof.mp disj_elim_proof $ tertium_non_daturAt_proof fl B)
                _)
          . apply export_proof
            apply atestfalse
          . apply export_proof
            apply imp_trans_proof
            . apply atesttrue
            . let C' : ((ℋ⟨mkConfig⟩(vs, mem) ⋀ ℋ@ fl B) ⟶ (ℋ⟨mkConfig⟩(vs, mem) ⋀ ℋ@ fl B).existClosure (⟨B ⬝ vs, mem⟩).FV).Context (∼ ℋ⟨PDLTest⟩(ℋNom fl), (ℋ⟨mkConfig⟩(vs, mem) ⋀ ℋ@ fl B) ⟶ (ℋ⟨mkConfig⟩(vs, mem) ⋀ ℋ@ fl B).existClosure (⟨B ⬝ vs, mem⟩).FV) := .tail .refl
              apply Proof.mp (.k _ _ _ _ C')
              apply Proof.ug C'
              apply insertExistCl
        . admit


end Rules
