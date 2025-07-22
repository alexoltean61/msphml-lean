import Hybrid.Proof
import Hybrid.Semantics

namespace Completeness

open Completeness

variable {α : Type u}
variable {β : Type v}

/--
  TODO SECTION:
    Signature / Symbols extensions and embeddings.
    Properties preserved by embeddings.
-/
structure Symbols.morphism (S₁ : Symbols α) (S₂ : Symbols β) : Type max (u+1) (v+1) where
  morph_sort : S₁.signature.S → S₂.signature.S
  morph_op {dom rng} : S₁.signature.Sig dom rng → S₂.signature.Sig (dom.map morph_sort) (morph_sort rng)
  morph_N    {st} : S₁.signature.N st → S₂.signature.N (morph_sort st)
  morph_prop {st} : S₁.prop st → S₂.prop (morph_sort st)
  morph_nom  {st} : S₁.nom st → S₂.nom (morph_sort st)
  morph_svar {st} : S₁.svar st → S₂.svar (morph_sort st)

structure Symbols.embedding (S₁ : Symbols α) (S₂ : Symbols β) where
  m : S₁.morphism S₂
  sort_inj : m.morph_sort.Injective
  op_inj   : ∀ dom rng, (@m.morph_op dom rng).Injective
  N_inj    : ∀ st, (@m.morph_N st).Injective
  prop_inj : ∀ st, (@m.morph_prop st).Injective
  nom_inj  : ∀ st, (@m.morph_nom st).Injective
  svar_inj : ∀ st, (@m.morph_svar st).Injective

infix:50 "↪" => Symbols.embedding

section Helpers

  variable {S₁ : Symbols α}
  variable {S₂ : Symbols β}
  variable {s : S₁.signature.S}

  def Symbols.morphism.morph_nominal (nom : S₁.nominal s) (m : S₁.morphism S₂) : S₂.nominal (m.morph_sort s) :=
    match nom with
    | .inl n => m.morph_N n
    | .inr n => m.morph_nom n

  def Symbols.morphism.morph_formula {sorts : List S₁.signature.S} (φ : FormL S₁ sorts) (m : S₁.morphism S₂) : FormL S₂ (sorts.map m.morph_sort) :=
    match φ with
    | .prop p   => .prop $ m.morph_prop p
    | .nom  n   => .nom $ m.morph_nominal n
    | .svar x   => .svar $ m.morph_svar x
    | .or φ ψ   => .or (m.morph_formula φ) (m.morph_formula ψ)
    | .neg φ    => .neg $ m.morph_formula φ
    | @FormL.at _ _ _ s k φ   => ℋ@[[(m.morph_sort s)]] (m.morph_nominal k) (m.morph_formula φ)
    | .bind x φ => .bind (m.morph_svar x) (m.morph_formula φ)
    | .appl σ φ => .appl (m.morph_op σ) (m.morph_formula φ)
    | .cons φ ψ => .cons (m.morph_formula φ) (m.morph_formula ψ)

  def Symbols.morphism.morph_premise (Γ : PremiseSet S₁ s) (m : S₁.morphism S₂) : PremiseSet S₂ (m.morph_sort s) :=
    { m.morph_formula φ | φ ∈ Γ }

  abbrev Symbols.embedding.morph_formula (φ : Form S₁ s) (m : S₁ ↪ S₂) : Form S₂ (m.m.morph_sort s) :=
    m.m.morph_formula φ

  abbrev Symbols.embedding.morph_premise (Γ : PremiseSet S₁ s) (m : S₁ ↪ S₂) : PremiseSet S₂ (m.m.morph_sort s) :=
    m.m.morph_premise Γ

  section ClassicalRequired

    open Classical

    noncomputable def Symbols.morphism.morph_axiom (Λ : AxiomSet S₁) (m : S₁.morphism S₂) : AxiomSet S₂ :=
      λ s => if h : ∃ s_inv, s = m.morph_sort s_inv then
                { h.choose_spec ▸ m.morph_formula φ | φ ∈ Λ h.choose }
             else { }

    abbrev Symbols.embedding.morph_axiom (Λ : AxiomSet S₁) (m : S₁ ↪ S₂) : AxiomSet S₂ :=
      m.m.morph_axiom Λ

  end ClassicalRequired

  notation:50 emb:lead "+" s:arg => Symbols.morphism.morph_sort (Symbols.embedding.m emb) s
  notation:50 emb:lead "+" φ:arg => Symbols.embedding.morph_formula φ emb
  notation:50 emb:lead "+" Γ:arg => Symbols.embedding.morph_premise Γ emb
  notation:50 emb:lead "+" Λ:arg => Symbols.embedding.morph_axiom Λ emb

end Helpers

section Lemmas

  variable {β : Type u}
  variable {S₁ : Symbols α}
  variable {s : S₁.signature.S}
  variable {Λ : AxiomSet S₁}
  variable {S₂ : Symbols β}
  variable {m : S₁ ↪ S₂}

  lemma SatLift {Γ : PremiseSet S₁ s} :
    (m+ Γ).satisfiable (m+ Λ).Models ↔ Γ.satisfiable Λ.Models := by
    apply Iff.intro
    . intro ⟨M_plus, ⟨g_plus, ⟨w_plus, h⟩⟩⟩

      admit
    . intro ⟨M, ⟨g, ⟨w, h⟩⟩⟩
      admit

  lemma ProvableLift [DecidableEq α] [DecidableEq β] {φ : Form S₁ s} :
    ⊢(m+ Λ, m+ s) (m+ φ) ↔ ⊢(Λ, s) φ := by

      admit

end Lemmas

section NewNominals
  /-
    In this section, we (nonconstructively) define the extension of a signature with a countable set of new nominals,
      and prove the new signature properly embeds the original one.

    The main statement is `theorem Symbols.new_nominals`.
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

  lemma Set.Elem.image_preimage_inv {S : Set α} : (@Set.Elem.preimage α S) ∘ Set.Elem.image = id := by
    funext
    apply Set.Elem.image_preimage_inv'

  theorem Symbols.new_nominals (S₁ : Symbols α) : ∃ S₂ : Symbols (ℕ ⊕ α), Nonempty (S₁ ↪ S₂) :=
    ⟨
      {
        signature := {
          S := S₁.signature.S.embed
          Sig := λ dom rng =>
            (S₁.signature.Sig dom.preimage rng.preimage).embed,
          N := λ st =>
            (S₁.signature.N st.preimage).embed,
          sortsCtbl := by
            apply Countable.mk
            have ⟨S₁_f, S₁_f_inj⟩ := S₁.signature.sortsCtbl.exists_injective_nat'
            let f : S₁.signature.S.embed → ℕ := S₁_f ∘ Set.Elem.preimage
            exists f
            rw [Function.Injective.of_comp_iff]
            . exact Set.Elem.preimage_injective
            . exact S₁_f_inj,
          opsCtbl := by
            intro dom rng
            apply Countable.mk
            have ⟨S₁_f, S₁_f_inj⟩ := (S₁.signature.opsCtbl dom.preimage rng.preimage).exists_injective_nat'
            let f : (S₁.signature.Sig dom.preimage rng.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
            exists f
            rw [Function.Injective.of_comp_iff]
            . exact Set.Elem.preimage_injective
            . exact S₁_f_inj,
          nomCtbl := by
            intro st
            apply Countable.mk
            have ⟨S₁_f, S₁_f_inj⟩ := (S₁.signature.nomCtbl st.preimage).exists_injective_nat'
            let f : (S₁.signature.N st.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
            exists f
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
            apply Countable.mk
            have ⟨S₁_f, S₁_f_inj⟩ := (S₁.propCtbl st.preimage).exists_injective_nat'
            let f : (S₁.prop st.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
            exists f
            rw [Function.Injective.of_comp_iff]
            . exact Set.Elem.preimage_injective
            . exact S₁_f_inj,
        nomCtbl := by
            intro st
            rw [Set.countable_union]
            apply And.intro
            . apply Countable.mk
              have ⟨S₁_f, S₁_f_inj⟩ := (S₁.nomCtbl st.preimage).exists_injective_nat'
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
            apply Countable.mk
            have ⟨S₁_f, S₁_f_inj⟩ := (S₁.svarCtbl st.preimage).exists_injective_nat'
            let f : (S₁.svar st.preimage).embed → ℕ := S₁_f ∘ Set.Elem.preimage
            exists f
            rw [Function.Injective.of_comp_iff]
            . exact Set.Elem.preimage_injective
            . exact S₁_f_inj,
        propNonEmpty := λ s => ⟨(S₁.propNonEmpty s.preimage).default.image⟩
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

end NewNominals

end Completeness
