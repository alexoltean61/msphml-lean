import Hybrid.Semantics
import Hybrid.Completeness.Lindenbaum.Sets

namespace Completeness

open Completeness

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s t : symbs.signature.S}

@[simp]
abbrev NamedPastedWitnessedMCS.nominal_eq (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) (i j : symbs.nominal s) : Prop := ℋ@ i j ∈ Γ.set

@[refl]
abbrev NamedPastedWitnessedMCS.nominal_eq_refl (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) : ∀ (x : Symbols.nominal s), Γ.nominal_eq s x x := sorry

@[symm]
abbrev NamedPastedWitnessedMCS.nominal_eq_symm (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) : ∀ {x y : Symbols.nominal s}, Γ.nominal_eq s x y → Γ.nominal_eq s y x := sorry

@[trans]
abbrev NamedPastedWitnessedMCS.nominal_eq_trans (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) : ∀ {x y z : Symbols.nominal s}, Γ.nominal_eq s x y → Γ.nominal_eq s y z → Γ.nominal_eq s x z := sorry

def nominal_eq.eqv {Γ : NamedPastedWitnessedMCS symbs t Λ} : Equivalence (Γ.nominal_eq s) where
  refl := Γ.nominal_eq_refl s
  symm := Γ.nominal_eq_symm s
  trans := Γ.nominal_eq_trans s

@[simp]
instance NamedPastedWitnessedMCS.nominalSetoid (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) : Setoid (symbs.nominal s) where
  r := Γ.nominal_eq s
  iseqv := nominal_eq.eqv

def WProd.to_args : WProd symbs.nominal sorts → FormL symbs sorts :=
  match sorts with
  | []     => PEmpty.elim
  | _ :: t =>
      match t with
      | []     => λ i     => ℋNom i
      | _ :: _ => λ i     => (ℋNom i.1).cons (to_args i.2)

def WProd.to_quotient (Γ : NamedPastedWitnessedMCS symbs s Λ) : WProd symbs.nominal sorts → WProd (λ s => Quotient (Γ.nominalSetoid s)) sorts :=
  match sorts with
  | []     => PEmpty.elim
  | _ :: t =>
      match t with
      | []     => λ i     => ⟦i⟧
      | _ :: _ => λ i     => ⟨⟦i.1⟧, to_quotient Γ i.2⟩

@[simp]
def NamedPastedWitnessedMCS.HenkinModel (Γ : NamedPastedWitnessedMCS symbs s Λ) : Model symbs where
  «Fr» := {
    W  := λ s => Quotient (Γ.nominalSetoid s),
    R  := λ {dom _} σ =>
        match dom with
        | [ ]    => { }
        | _ :: _ => { ⟨q, qs⟩ | ∃ j, ∃ (js : WProd symbs.nominal _), ℋ@ j (ℋ⟨σ⟩ js.to_args) ∈ Γ.set ∧ (⟦j⟧ = q ∧ js.to_quotient Γ = qs) },
    Nm := λ n => ⟦.ctNom n⟧,
    WNonEmpty := λ s => ⟨⟦(symbs.signature.nNonEmpty s).default⟧⟩,
    WDisjoint := sorry
  }
  Vₚ   := λ {t} p => { q | ∃ j : symbs.nominal t, ℋ@ j (ℋProp p) ∈ Γ.set ∧ ⟦j⟧ = q }
  Vₙ   := λ j => ⟦.inr j⟧

noncomputable def NamedPastedWitnessedMCS.HenkinAsgn (Γ : NamedPastedWitnessedMCS symbs s Λ) : Assignment Γ.HenkinModel :=
  λ x => ⟦Classical.choose $ Γ.witnessed.2 x⟧

lemma WProd.to_quotient_select {Γ : NamedPastedWitnessedMCS symbs s Λ} {φ : Form symbs t} {ψ : FormL symbs sorts} (ws : WProd symbs.nominal sorts) (C : φ.Context ψ) : (ws.to_quotient Γ).select C = ⟦ws.select C⟧ := by
  admit

lemma WProd.eq {ws ws' : WProd f ss} : ws = ws' ↔ ∀ {ψ : FormL symbs ss} {e : ψ.Elem}, ws.select e.ctx = ws'.select e.ctx := by
  apply Iff.intro
  . intros

    admit
  . intros
    admit

lemma WProd.to_quotient_eq_helper {Γ : NamedPastedWitnessedMCS symbs s Λ} {ws : WProd symbs.nominal sorts} {qs : WProd (λ s => Quotient (Γ.nominalSetoid s)) sorts} : ws.to_quotient Γ = qs ↔ ∀ {ψ : FormL symbs sorts} {e : ψ.Elem}, ⟦ws.select e.ctx⟧ = qs.select e.ctx := by
  apply Iff.intro
  . intro h ψ e
    rw [←to_quotient_select]
    rw [WProd.eq] at h
    apply h
  . rw [WProd.eq]
    intro h ψ e
    rw [to_quotient_select]
    apply h

lemma WProd.to_quotient_eq {Γ : NamedPastedWitnessedMCS symbs s Λ} {ws : WProd symbs.nominal sorts} {qs : WProd (λ s => Quotient (Γ.nominalSetoid s)) sorts} :
  ws.to_quotient Γ = qs ↔
  ∀ {ψ : FormL symbs sorts} {e : ψ.Elem}, ∃ j : symbs.nominal e.sort, ℋ@ j (ws.select e.ctx) ∈ Γ.set ∧ ⟦j⟧ = qs.select e.ctx := by
  rw [to_quotient_eq_helper]
  apply Iff.intro
  . intro h ψ e
    specialize @h ψ e
    have ⟨j, h_rep⟩ := (qs.select e.ctx).exists_rep
    simp only [NamedPastedWitnessedMCS.nominalSetoid, ← h_rep, Quotient.eq] at h
    symm at h
    exists j
  . intro h ψ e
    specialize @h ψ e
    match h with
    | ⟨j, ⟨h_equiv, h_rep⟩⟩ =>
      simp only [NamedPastedWitnessedMCS.nominalSetoid, ← h_rep, Quotient.eq]
      symm
      exact h_equiv

end Completeness
