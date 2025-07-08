import Hybrid.Proof
import Hybrid.Semantics
import Hybrid.Soundness.Lemmas

namespace Soundness

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
  | kAt =>
      intro M g w
      simp only [Sat.implies, Sat.at, imp_self]
  | agree =>
      intro M g w
      simp only [Sat.iff, Sat.at]
  | selfDual =>
      intro M g w
      simp only [Sat.iff, Sat.at, Sat.neg, not_not]
  | intro =>
      intro M g w
      simp only [Sat.implies, Sat.nom, Sat.iff, Sat.at]
      intro h
      rw [h]
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
  | name x =>
      rename_i s
      intro M g w
      simp only [WProd] at w
      simp only [Sat.exists, Sat.svar]
      let g' : Assignment M :=
            λ {t : symbs.signature.S} (y : symbs.svar t) =>
              if h : s = t then
                if h ▸ x = y then
                  h ▸ w
                else g y
              else g y
      exists g'
      apply And.intro
      . unfold g'
        unfold Assignment.variant
        aesop
      . simp only [↓reduceDIte, ↓reduceIte, g']
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
          simp only [WProd.select_iso (FormL.Context.iso_trans' h_iso h_iso'), Sat.implies] at hw1
          specialize hw1 hw2
          have ⟨ctx_w3, iso⟩ := FormL.Context.subst_iso ctx_w2 h_iso' ψ
          simp only [WProd.select_iso iso] at hw1
          rename_i s' _ _ _
          exists s'
          exists ψ
          exists ctx_w3
        . have ⟨ctx_w3, iso⟩ := FormL.Context.subst_not_iso' ctx_w2 h_iso' ψ
          simp only [WProd.select_iso iso] at hw2
          rename_i form _
          exists τ₂
          exists form
          exists ctx_w3
      . have ⟨ctx_w3, iso⟩ := ctx.subst_not_iso ctx_w1 h_iso ψ
        simp only [WProd.select_iso iso] at hw1
        rename_i form _ _
        exists τ₁
        exists form
        exists ctx_w3
  | barcan x φ σ C h =>
      intro M g w
      simp only [Sat.implies]
      intro h2
      simp only [Sat.forall, Sat.applDual] at h2 ⊢
      rw [forall₂_swap] at h2
      intro ws wRws
      specialize h2 ws wRws
      rename_i s' _ _ _
      apply Or.elim ((BarcanLemma g h) h2)
      . clear h2
        intro h2
        exists s'
        exists ℋ∀ x φ
        exists (ℋ∀ x φ).subst_to_ctx C
        simp only [Sat.forall]
        intro g' is_variant
        specialize h2 g' is_variant
        rw [WProd.select_iso]
        . exact h2
        . apply (ℋ∀ x φ).subst_to_ctx_iso
      . clear h2
        intro ⟨sort, ⟨arg, ⟨C', h_sat⟩⟩⟩
        -- C' points to a single argument in the list:
        --  φ₁, ..., ℋ⊥, ..., φₙ
        --
        -- h_sat ensures that the argument picked out by C' is satisfied
        -- in its respective world.
        --
        -- We want to show that there is a formula in the list:
        --  φ, ..., ℋ∀ x φ, ..., φₙ
        -- that is satisfied in its respective world.
        exists sort
        exists arg
        by_cases C_iso_C' : C.iso C'
        . -- In this case, the argument selected by C' is ℋ⊥,
          -- whose satisfaction by h_sat leads to a contradiction
          have := C.iso_subst_sorts C_iso_C'
          subst this
          have := C.iso_subst C_iso_C'
          subst this
          simp only [Sat.bot] at h_sat
        . -- In this case, C' selects some argument other than ℋ⊥.
          -- Since this necessarily is also an argument ocurring in:
          --   φ, ..., ℋ∀ x φ, ..., φₙ,
          -- then by h_sat, we have our desired conclusion.
          have ⟨C'', C'_iso_C''⟩ := C.subst_not_iso' C' C_iso_C' (ℋ∀ x φ)
          exists C''
          rw [WProd.select_iso]
          . exact h_sat
          . symm
            exact C'_iso_C''
  | barcanAt =>
      intro M g w
      simp only [Sat.implies, Sat.forall, Sat.at, imp_self]
  | nom =>
      intro M g w
      simp only [Sat.implies, Sat.and, Sat.at, Sat.svar, Sat.nom, and_imp]
      intro h1 h2
      rw [h1, h2]
  | broadcastS _ _ h =>
      rename_i s₁ _ _ _ _ _
      intro M g w
      simp only [Sat.at]
      specialize h M g ((M.1).Fr.WNonEmpty s₁).default
      simp only [Sat.at] at h
      exact h
  | genAt _ _ _ h =>
      rename_i j _
      intro M g w
      simp only [Sat.at]
      specialize h M g ((M.1).VNom j)
      exact h
  | paste C _ h =>
      intro M g w
      specialize h M g w
      simp only [Sat.and, Sat.at, Sat.implies] at h
      have ⟨k_φ, imp⟩ := h
      clear h

      simp only [Sat.implies, Sat.at, Sat.appl]
      intro ⟨ws, ⟨sat_χ, jRws⟩⟩

      apply imp
      simp only [Sat.appl]
      exists ws

      apply And.intro
      . rw [Sat.context] at sat_χ ⊢
        intro s' τ C'
        by_cases is_iso : C.iso C'
        . have := C.iso_subst_sorts is_iso
          symm at this
          subst this
          have := C.iso_subst is_iso
          symm at this
          subst this
          symm at is_iso
          rw [WProd.select_iso is_iso]

          specialize sat_χ C
          simp only [Sat.nom] at sat_χ
          rw [sat_χ]
          exact k_φ
        . have ⟨C'', C''_iso_C'⟩ := C.subst_not_iso'' is_iso
          rw [WProd.select_iso C''_iso_C']
          exact sat_χ C''
      . exact jRws
  | gen _ _ h =>
      intro M g w
      simp only [Sat.forall]
      intro g' _
      specialize h M g' w
      exact h
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

end Soundness
