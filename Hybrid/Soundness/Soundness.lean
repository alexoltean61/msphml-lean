import Hybrid.Proof
import Hybrid.Semantics

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

theorem Soundness {Λ : AxiomSet symbs} : ⊢(Λ, s) φ → ⊨Mod(Λ) φ := by
  intro pf
  induction pf with
  | ax ψ =>
      intro M g w
      apply M.2
      exact ψ.2
  | prop1 =>
      intro M g w
      simp only [Sat.implies]
      intro h1 _
      assumption
  | prop2 =>
      intro M g w
      simp only [Sat.implies]
      intros
      repeat apply_assumption
  | prop3 =>
      intro M g w
      simp only [Sat.implies, Sat.neg]
      intro
      contrapose
      assumption
  | mp min maj ih1 ih2 =>
      intro M g w
      apply (Sat.implies.mp (ih1 M g w))
      apply ih2
  | ug ctx _ ih =>
      intro M g w
      rw [Sat.applDual]
      intro ws wRws
      rename_i φ _
      rename_i s' _ _ _ _ _ _
      exists s'
      exists φ
      exists ctx
      specialize ih M g (ws.select ctx)
      exact ih
  | back j φ ψ σ ctx =>
      intro M g w
      rw [Sat.implies]
      intro h
      simp only [Sat] at h ⊢
      have ⟨ws, ⟨h, wRws⟩⟩ := h
      rw [Sat.context] at h
      specialize h ctx
      simp only [Sat.at] at h
      exact h
  | k φ ψ χ σ ctx =>
      intro M g w
      simp only [Sat.implies, Sat.applDual]
      intro h1 h2
      intro ws wRws
      specialize h1 ws wRws
      specialize h2 ws wRws
      -- How the proof works from here:
      --  Case analysis by h1's and h2's witnesses.
      --  1. If h1 and h2 are both witnessed by the same context,
      --        (i.e., the index of the argument φᵢ in the argument list φ₀, ..., φₙ)
      --     AND that is the context of (φ ⟶ ψ)'s ocurrence within χ,
      --     then we know that the world witnessed by h1 and h2 is also the same,
      --        and we can apply MP at it.
      --     Thus, at that world, we know ψ is satisfied.
      --     Since that world's index will also be the same as ψ's occurrence within ctx[ψ],
      --        it's clear that there exists an index whose world satisfies the respective argument, as intended.
      --  2. If either h1 or h2 are not witnesed by the context of (φ ⟶ ψ)'s ocurrence within χ, then the proof is already
      --        complete.
      have ⟨τ₁, hw1⟩ := h1
      have ⟨_, ⟨ctx_w1, hw1⟩⟩ := hw1
      have ⟨τ₂, hw2⟩ := h2
      have ⟨_, ⟨ctx_w2, hw2⟩⟩ := hw2
      clear h1 h2
      by_cases h_iso : ctx.iso ctx_w1
      -- This proof with contexts is too technical! It needs to be more human readable!
      -- Please consider refactoring it with indices (as sketched in the comment above), instead of contexts and context iso's.
      . have := ctx.if_iso_sorts ctx_w1 h_iso
        subst this
        have := ctx.if_iso ctx_w1 h_iso
        subst this
        by_cases h_iso' : ctx.iso ctx_w2
        . have := ctx.iso_subst_sorts h_iso'
          subst this
          have := (ctx.iso_subst h_iso').symm
          subst this
          simp only [WProd.select_iso.mp (FormL.Context.iso_trans h_iso h_iso'), Sat.implies] at hw1
          specialize hw1 hw2
          have ⟨ctx_w3, iso⟩ := FormL.Context.subst_iso ctx_w2 h_iso' ψ
          simp only [WProd.select_iso.mp iso] at hw1
          rename_i s' _ _ _
          exists s'
          exists ψ
          exists ctx_w3
        . have ⟨ctx_w3, iso⟩ := FormL.Context.subst_not_iso ctx_w2 h_iso' ψ
          simp only [WProd.select_iso.mp iso] at hw2
          rename_i form _
          exists τ₂
          exists form
          exists ctx_w3
      . have ⟨ctx_w3, iso⟩ := ctx.subst_not_iso' ctx_w1 h_iso ψ
        simp only [WProd.select_iso.mp iso] at hw1
        rename_i form _ _
        exists τ₁
        exists form
        exists ctx_w3
  | barcan x φ σ C h =>
      admit
  | paste ctx h1 h2 h3 _ ih =>
      intro M g w
      rw [Sat.implies]
      intro h4
      simp only [Sat] at h4
      have ⟨ws, ⟨sat, inR⟩⟩ := h4
      admit
  | _  => sorry

-- Strong model soundness
theorem ModelSoundness {Λ : AxiomSet symbs} : Γ ⊢(Λ) φ → Γ ⊨Mod(Λ) φ := by
  intro ⟨forms, pf⟩
  apply Valid.conjunction_entails
  exists forms
  apply Soundness
  exact pf

-- Strong frame soundness
theorem FrameSoundness {Λ : AxiomSet symbs} : Γ ⊢(Λ) φ → Γ ⊨Fr(Λ) φ := by
  intro pf
  apply Entails.if_model_frame
  apply ModelSoundness
  exact pf
