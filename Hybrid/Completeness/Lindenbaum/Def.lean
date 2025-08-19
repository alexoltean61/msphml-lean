import Hybrid.Completeness.Lindenbaum.Sets
import Hybrid.Completeness.Lindenbaum.Enumeration

namespace Completeness

open Completeness
open Encodable
open Denumerable

variable {α β : Type u}
variable [DecidableEq α] [β_deq : DecidableEq β]
variable {S : Symbols α}
variable {s : S.signature.S}
variable (ext : @S.nominal_extension α β β_deq β)

abbrev PremiseSet.embed (Γ : PremiseSet S s) (Λ : AxiomSet S) : ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ) :=
  ⟨ext.m+ Γ, enough_nominals_embed⟩

open Classical

noncomputable def PremiseSet.Lindenbaum (Λ : AxiomSet S) (Γ : PremiseSet S s) : ℕ → ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ)
| 0       =>
    let Γ' : ExtendiblePremiseSet _ _ (ext.m+ Λ) := ⟨(Γ.embed ext Λ).set ∪ (Γ.embed ext Λ).at_witness_vars, enough_nominals_at_witness⟩
    ⟨Γ'.set ∪ { ℋNom (Γ'.prod_even_nominal _ 0 0) }, enough_nominals_singleton⟩
| .succ i =>
    let φ_i : Form ext.target (ext.m+ s) := ofNat _ i
    let Γ' : ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ) := ⟨(PremiseSet.Lindenbaum Λ Γ i).set ∪ { φ_i }, enough_nominals_singleton⟩
    if ((PremiseSet.Lindenbaum Λ Γ i).set ∪ { ofNat _ i }).consistent (ext.m+ Λ) then
      match φ_i with
      -- note that the sort of new nominal k is the sort of x, and may differ from (ext.m+ s)
      | ℋ@ j (ℋ∃ x φ) => ⟨Γ'.set ∪ { ℋ@ j φ[(Γ'.prod_even_nominal _ i 0) // x]}, enough_nominals_singleton⟩
      -- note that the sort of new nominal k is the sort s' of φ, and may differ from (ext.m+ s)
      | ℋ@ j (ℋ⟨σ⟩ χ) => ⟨Γ'.set ∪ Γ'.paste_args j σ χ i, enough_nominals_paste⟩
      | _ => Γ'
    else PremiseSet.Lindenbaum Λ Γ i

def PremiseSet.LindenbaumExtension (Λ : AxiomSet S) (Γ : PremiseSet S s) : PremiseSet ext.target (ext.m+ s) :=
  { φ | ∃ i : ℕ, φ ∈ (Γ.Lindenbaum ext Λ i).set }

end Completeness
