import Hybrid.Completeness.Lindenbaum.Expansion

namespace Completeness

open Completeness

variable {α : Type u}
variable {symbs : Symbols α}

def Nat.sort : ℕ → symbs.signature.S := λ n =>
  match symbs.signature.sortsCtbl.decode n with
  | some st => st
  | none => symbs.signature.sNonEmpty.default

lemma Nat.sort_surj : (@Nat.sort α symbs).Surjective := by
  intro st
  exists symbs.signature.sortsCtbl.encode st
  simp only [Nat.sort, Encodable.encodek]

/-
def Nat.form (n : ℕ) : ℕ → Form symbs n.sort := sorry

lemma Nat.form_surj : ∀ s, (@Nat.form α symbs s).Surjective := sorry
-/

instance form_denumerable (s : symbs.signature.S) : Denumerable (Form symbs s) := sorry

instance Nat.form (s : symbs.signature.S) : ℕ → Form symbs s := Denumerable.ofNat (Form symbs s)

lemma Nat.form_surj : ∀ s, (@Nat.form α symbs s).Surjective := sorry
