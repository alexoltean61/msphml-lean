import Hybrid.Semantics
import Hybrid.Completeness.Lindenbaum.Sets

namespace Completeness

open Completeness

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s t : symbs.signature.S}

def NamedPastedWitnessedMCS.HenkinModel (Γ : NamedPastedWitnessedMCS symbs s Λ) : Models.Ax Λ := sorry

def NamedPastedWitnessedMCS.HenkinAsgn (Γ : NamedPastedWitnessedMCS symbs s Λ) : Assignment (Γ.HenkinModel).1 := sorry

def nom_to_w (j : symbs.nominal t) (Γ : NamedPastedWitnessedMCS symbs s Λ) : (Γ.HenkinModel).1.Fr.W t := sorry

notation "|" j "|" => nom_to_w j

end Completeness
