import Hybrid.Semantics
import Hybrid.Completeness.Lindenbaum.Sets

namespace Completeness

open Completeness

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s t : symbs.signature.S}

abbrev NamedPastedWitnessedMCS.nominal_eq (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) (i j : symbs.nominal s) : Prop := ℋ@ i j ∈ Γ.set

def nominal_eq.eqv {Γ : NamedPastedWitnessedMCS symbs t Λ} : Equivalence (Γ.nominal_eq s) where
  refl := by
    admit
  symm := by
    admit
  trans := by
    admit

instance NamedPastedWitnessedMCS.nominalSetoid (Γ : NamedPastedWitnessedMCS symbs t Λ) (s : symbs.signature.S) : Setoid (symbs.nominal s) where
  r := Γ.nominal_eq s
  iseqv := nominal_eq.eqv

def WProd.to_args (Γ : NamedPastedWitnessedMCS symbs s Λ) : WProd symbs.nominal sorts → FormL symbs sorts :=
  match sorts with
  | []     => PEmpty.elim
  | _ :: t =>
      match t with
      | []     => λ i     => ℋNom i
      | _ :: _ => λ i     => (ℋNom i.1).cons (to_args Γ i.2)

def WProd.to_quotient (Γ : NamedPastedWitnessedMCS symbs s Λ) : WProd symbs.nominal sorts → WProd (λ s => Quotient (Γ.nominalSetoid s)) sorts :=
  match sorts with
  | []     => PEmpty.elim
  | _ :: t =>
      match t with
      | []     => λ i     => ⟦i⟧
      | _ :: _ => λ i     => ⟨⟦i.1⟧, to_quotient Γ i.2⟩

def NamedPastedWitnessedMCS.HenkinModel (Γ : NamedPastedWitnessedMCS symbs s Λ) : Model symbs where
  «Fr» := {
    W  := λ s => Quotient (Γ.nominalSetoid s),
    R  := λ {dom _} σ =>
        match dom with
        | [ ]    => { } -- constant σ case. TODO: make sure to support constant operators as formulas as well
        | _ :: _ => { ⟨q, qs⟩ | ∃ j, ∃ (js : WProd symbs.nominal _), ℋ@ j (ℋ⟨σ⟩ (js.to_args Γ)) ∈ Γ.set ∧ (⟦j⟧ = q ∧ js.to_quotient Γ = qs) },
    Nm := λ n => ⟦.inl n⟧,
    WNonEmpty := λ s => ⟨⟦(symbs.signature.nNonEmpty s).default⟧⟩
  }
  Vₚ   := λ {t} p => { q | ∃ j : symbs.nominal t, ℋ@ j (ℋProp p) ∈ Γ.set ∧ ⟦j⟧ = q }
  Vₙ   := λ j => ⟦.inr j⟧

noncomputable def NamedPastedWitnessedMCS.HenkinAsgn (Γ : NamedPastedWitnessedMCS symbs s Λ) : Assignment Γ.HenkinModel :=
  λ x => ⟦Classical.choose $ Γ.witnessed.2 x⟧

def nom_to_w (j : symbs.nominal t) (Γ : NamedPastedWitnessedMCS symbs s Λ) : Γ.HenkinModel.Fr.W t := ⟦j⟧

end Completeness
