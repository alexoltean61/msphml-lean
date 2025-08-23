import Hybrid.Completeness.Lindenbaum.Expansion.Lemmas

open Completeness

/-
  In this file, we (nonconstructively) define the extension of a signature with a countable set of new nominals,
    and prove the new signature properly embeds the original one.

  The main definition is `Symbols.new_nominals`.

  Using this definition, we provide an `Inhabited` instance for `nominal_extension`.
-/

abbrev Set.embed : Set α → Set (ℕ ⊕ α) := λ S => { Sum.inr e | e ∈ S }

abbrev Set.Elem.image {S : Set α} (e : S) : S.embed :=
  ⟨Sum.inr e, by simp only [Set.mem_setOf_eq, Sum.inr.injEq, exists_eq_right, Subtype.coe_prop]⟩

noncomputable abbrev Set.Elem.preimage {S : Set α} (e : S.embed) : S :=
  ⟨e.2.choose, e.2.choose_spec.1⟩

noncomputable abbrev List.preimage {S : Set α} (L : List S.embed): List S := L.map Set.Elem.preimage

lemma Set.Elem.preimage_injective {S : Set α} : (@Set.Elem.preimage α S).Injective := by
  intro e1 e2 h
  obtain ⟨e1, pf1⟩ := e1
  obtain ⟨e2, pf2⟩ := e2
  simp only [Set.mem_setOf_eq, Subtype.mk.injEq]
  cases e1 with
  | inl n =>
    simp [Set.embed] at pf1
  | inr a =>
    cases e2 with
    | inl n =>
      simp [Set.embed] at pf2
    | inr b =>
      simp only [Sum.inr.injEq]
      have a_choice := pf1.choose_spec.2
      have b_choice := pf2.choose_spec.2
      simp at a_choice b_choice h
      rw [←a_choice, ←b_choice, h]

lemma Set.Elem.image_preimage_inv' {S : Set α} (e : S) : e.image.preimage = e := by
  have := e.image.2.choose_spec.2
  obtain ⟨e, pf⟩ := e
  simp_all only [Subtype.mk.injEq, Sum.inr.injEq]

lemma Set.Elem.image_preimage_inv'' {S : Set α} (e : S.embed) : e.preimage.image = e := by
  obtain ⟨e, pf⟩ := e
  cases e with
  | inl n => simp at pf
  | inr n =>
      have := pf.choose_spec.2
      simp at this ⊢
      exact this

lemma Set.Elem.image_preimage_inv {S : Set α} : (@Set.Elem.preimage α S) ∘ Set.Elem.image = id := by
  funext
  apply Set.Elem.image_preimage_inv'

noncomputable instance Symbols.new_nominals (S₁ : Symbols α) : Σ S₂ : Symbols (ℕ ⊕ α), Inhabited (S₁ ↪ S₂) :=
  ⟨
    {
      signature := {
        S := S₁.signature.S.embed
        Sig := λ dom rng =>
          (S₁.signature.Sig dom.preimage rng.preimage).embed,
        N := λ st =>
          (S₁.signature.N st.preimage).embed,
        sortsCtbl := by
          apply @Encodable.ofInj _ ℕ
          let S₁_f := S₁.signature.sortsCtbl.encode
          let S₁_f_inj := S₁.signature.sortsCtbl.encode_injective
          let f : S₁.signature.S.embed → ℕ := S₁_f ∘ Set.Elem.preimage
          rw [Function.Injective.of_comp_iff]
          . exact Set.Elem.preimage_injective
          . exact S₁_f_inj,
        opsCtbl := by
          intro dom rng
          apply @Encodable.ofInj _ ℕ
          let S₁_f := (S₁.signature.opsCtbl dom.preimage rng.preimage).encode
          let S₁_f_inj := (S₁.signature.opsCtbl dom.preimage rng.preimage).encode_injective
          let f : (S₁.signature.Sig dom.preimage rng.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
          rw [Function.Injective.of_comp_iff]
          . exact Set.Elem.preimage_injective
          . exact S₁_f_inj,
        nomCtbl := by
          intro st
          apply @Encodable.ofInj _ ℕ
          let S₁_f := (S₁.signature.nomCtbl st.preimage).encode
          let S₁_f_inj := (S₁.signature.nomCtbl st.preimage).encode_injective
          let f : (S₁.signature.N st.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
          rw [Function.Injective.of_comp_iff]
          . exact Set.Elem.preimage_injective
          . exact S₁_f_inj,
        sNonEmpty := ⟨S₁.signature.sNonEmpty.default.image⟩
      },
      prop := λ st =>
          (S₁.prop st.preimage).embed,
      nom := λ st =>
          (S₁.nom st.preimage).embed ∪ { Sum.inl n | n : ℕ },
      svar := λ st =>
          (S₁.svar st.preimage).embed,
      propCtbl := by
          intro st
          apply @Encodable.ofInj _ ℕ
          let S₁_f := (S₁.propCtbl st.preimage).encode
          let S₁_f_inj := (S₁.propCtbl st.preimage).encode_injective
          let f : (S₁.prop st.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
          rw [Function.Injective.of_comp_iff]
          . exact Set.Elem.preimage_injective
          . exact S₁_f_inj,
      nomCtbl := by
          intro st
          -- Easier if we prove Countable instead of Encodable,
          -- because we have the Set.countable_union lemma.
          -- This definition is nonconstructive anyway.
          apply Set.Countable.toEncodable
          rw [Set.countable_union]
          apply And.intro
          . apply Countable.mk
            let S₁_f := (S₁.nomCtbl st.preimage).encode
            let S₁_f_inj := (S₁.nomCtbl st.preimage).encode_injective
            let f : (S₁.nom st.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
            exists f
            rw [Function.Injective.of_comp_iff]
            . exact Set.Elem.preimage_injective
            . exact S₁_f_inj
          . rw [Set.countable_iff_exists_surjective]
            . exists (λ n => ⟨.inl n, by simp⟩)
              intro ⟨a, ⟨n, h⟩⟩
              exists n
              simp [h]
            . exists .inl 0
              simp,
      svarCtbl := by
          intro st
          apply Denumerable.ofEquiv ℕ
          apply Equiv.mk
          case toFun =>
              exact (S₁.svarCtbl st.preimage).eqv.toFun ∘ Set.Elem.preimage
          case invFun =>
              exact Set.Elem.image ∘ (S₁.svarCtbl st.preimage).eqv.invFun
          . intro x
            simp only [Set.coe_setOf, Equiv.invFun_as_coe, Equiv.toFun_as_coe,
              Function.comp_apply, Equiv.symm_apply_apply, Set.Elem.image_preimage_inv'']
          . intro x
            simp only [Set.coe_setOf, Equiv.toFun_as_coe, Equiv.invFun_as_coe,
              Function.comp_apply, Set.Elem.image_preimage_inv', Equiv.apply_symm_apply]
    },
    ⟨{
      m := {
        morph_sort := Set.Elem.image
        morph_op := λ σ =>
          ⟨Sum.inr σ,
          by simp; rw [Set.Elem.image_preimage_inv, Set.Elem.image_preimage_inv']; simp⟩,
        morph_N := λ j =>
          ⟨Sum.inr j,
          by simp; rw [Set.Elem.image_preimage_inv']; simp⟩,
        morph_prop := λ p =>
          ⟨Sum.inr p,
          by simp; rw [Set.Elem.image_preimage_inv']; simp⟩,
        morph_nom := λ j =>
          ⟨Sum.inr j,
          by simp; rw [Set.Elem.image_preimage_inv']; simp⟩,
        morph_svar :=  λ x =>
          ⟨Sum.inr x,
          by simp; rw [Set.Elem.image_preimage_inv']; simp⟩,
      },
      sort_inj := by
        simp
        intro _ _
        aesop,
      op_inj := by
        simp
        intros _ _ _ _ _
        aesop,
      N_inj := by
        simp
        intros _ _ _
        aesop,
      prop_inj := by
        simp
        intros _ _ _
        aesop,
      nom_inj := by
        simp
        intros _ _ _
        aesop,
      svar_inj := by
        simp
        intros _ _ _
        aesop
    }⟩
  ⟩

instance {S : Symbols α} {s : S.new_nominals.1.signature.S} : OfNat (S.new_nominals.1.nom s) (n : ℕ) where
  ofNat := ⟨.inl n, by simp [Symbols.new_nominals]⟩

instance {S : Symbols α} {s : S.new_nominals.1.signature.S} : Coe ℕ (S.new_nominals.1.nom s) where
  coe := λ n => ⟨.inl n, by simp [Symbols.new_nominals]⟩

noncomputable instance nominal_extension [deq : DecidableEq α] {S : Symbols α} : Inhabited (@S.nominal_extension _ (ℕ ⊕ α) (instDecidableEqSum) (ℕ ⊕ α)) := .mk $
  {
    target := S.new_nominals.1
    m := S.new_nominals.2.default
    unused_nominals := by
      intros
      refine (Equiv.ofBijective ?_ ?_).symm
      . exact (λ n => ⟨n, by simp only [default, Set.coe_setOf, Equiv.toFun_as_coe,
        Equiv.invFun_as_coe, Set.mem_setOf_eq, ne_eq, Subtype.forall, Subtype.mk.injEq,
        reduceCtorEq, not_false_eq_true, implies_true]⟩)
      . refine Function.bijective_iff_has_inverse.mpr ?_

        admit
  }
