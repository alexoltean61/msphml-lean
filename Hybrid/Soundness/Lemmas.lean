
import Hybrid.Semantics

namespace Soundness

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

section AgreementLemma

  lemma AgreementL1 {M : Model symbs} {φ : Form symbs s} {x : symbs.svar t} {g g' g_var : Assignment M} (agree_not_x : g.free_agree g' (ℋ∀ x φ)) (is_var : g_var.variant g x) : g_var.free_agree g' (ℋ∀ x φ) := by
    simp only [Assignment.free_agree] at agree_not_x
    simp only [Assignment.free_agree]
    intros t y h
    specialize agree_not_x y h
    rename_i s
    by_cases h_sort : s = t
    . subst h_sort
      by_cases h_var : x = y
      . subst h_var
        simp only [FormL.varOccursFree, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true] at h
      . simp only [Assignment.variant, ne_eq,] at is_var
        rw [←agree_not_x]
        exact is_var.1 y h_var
    . simp only [Assignment.variant, ne_eq,] at is_var
      rw [←agree_not_x]
      exact is_var.2 y h_sort

  lemma AgreementL2 {M : Model symbs} {φ : Form symbs s} {x : symbs.svar t} {g g' : Assignment M} (agree_not_x : g.free_agree g' (ℋ∀ x φ)) (agree_x : g x = g' x) : g.free_agree g' φ := by
    simp only [Assignment.free_agree, FormL.varOccursFree] at agree_not_x ⊢
    intro s y not_free
    by_cases h_sort : s = t
    . subst h_sort
      by_cases h_var : x = y
      . subst h_var
        exact agree_x
      . apply agree_not_x
        simp only [↓reduceDIte, Bool.if_false_left, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, decide_eq_false_iff_not]
        apply And.intro
        . intro h_abs
          symm at h_abs
          exact h_var h_abs
        . exact not_free
    . apply agree_not_x
      simp only [h_sort, ↓reduceDIte]
      exact not_free

  lemma Agreement {M : Model symbs} {φ : FormL symbs sorts} {ws : WProd M.Fr.W sorts} {g g' : Assignment M} (agree : g.free_agree g' φ) :
    (⟨M, g, ws⟩ ⊨ φ) ↔ ⟨M, g', ws⟩ ⊨ φ := by
    induction φ generalizing g g' with
    | prop =>
        simp only [Sat.prop]
    | nom =>
        simp only [Sat.nom]
    | svar x =>
        simp only [Sat.svar]
        specialize agree x
        simp only [FormL.varOccursFree, FormL.varOccurs, ↓reduceDIte, BEq.rfl, forall_const] at agree
        simp only [agree]
    | appl _ _ ih =>
        simp only [Sat.appl]
        simp only [Assignment.free_agree, FormL.varOccursFree] at agree
        rw [←Assignment.free_agree] at agree
        apply Iff.intro
        repeat {
          intro ⟨w, ⟨h1, h2⟩⟩
          exists w
          apply And.intro
          . specialize @ih w g g' agree
            first | rw [ih] at h1 | rw [ih]
            assumption
          . exact h2
        }
    | or φ ψ ih1 ih2 =>
        simp only [Sat.or]
        simp only [Assignment.free_agree, FormL.varOccursFree, Bool.or_eq_true] at agree
        have ⟨agree_φ, agree_ψ⟩ : g.free_agree g' φ ∧ g.free_agree g' ψ := by
          unfold Assignment.free_agree
          aesop
        clear agree
        apply Iff.intro
        repeat {
          intro h
          apply Or.elim h
          . intro h_left
            apply Or.inl
            specialize @ih1 ws g g' agree_φ
            first | rw [ih1] at h_left | rw [ih1]
            exact h_left
          . intro h_right
            apply Or.inr
            specialize @ih2 ws g g' agree_ψ
            first | rw [ih2] at h_right | rw [ih2]
            exact h_right
        }
    | neg φ ih =>
        simp only [Sat.neg]
        rw [Iff.not]
        simp only [Assignment.free_agree, FormL.varOccursFree] at agree
        rw [←Assignment.free_agree] at agree
        apply ih
        repeat assumption
    | bind x φ ih =>
        simp only [Sat.forall]
        apply Iff.intro
        . rename_i s _
          intro h variant_g' is_variant_g'
          let variant_g : Assignment M :=
            λ {t : symbs.signature.S} (y : symbs.svar t) =>
              if h : s = t then
                if h ▸ x = y then
                  variant_g' y
                else g y
              else g y
          have is_variant_g : variant_g.variant g x := by
            unfold Assignment.variant
            unfold variant_g
            aesop
          have agree_x : variant_g x = variant_g' x := by
            simp only [↓reduceDIte, ↓reduceIte, variant_g]
          specialize h variant_g is_variant_g
          -- By hypothesis "agree", we know that g and g' agree on all
          -- free variables in φ excepting x.
          -- Now: variant_g  is an x-variant of g
          --      variant_g' is an x-variant of g'
          -- So variant_g and variant_g' also agree on all free variables
          -- excepting x.
          --
          -- But you also have agree_x : variant_g x = variant_g'.
          -- Therefore, variant_g and variant_g' agree on all free variables in φ
          --
          -- So we apply the induction hypothesis to h and obtain the conclusion.
          have : variant_g.free_agree g' (ℋ∀ x φ) := AgreementL1 agree is_variant_g
          symm at this
          have : variant_g'.free_agree variant_g (ℋ∀ x φ) := AgreementL1 this is_variant_g'
          symm at this
          have : variant_g.free_agree variant_g' φ := AgreementL2 this agree_x
          specialize @ih ws variant_g variant_g' this
          rw [←ih]
          exact h
        . -- Analogous to the other case
          rename_i s _
          intro h variant_g is_variant_g
          let variant_g' : Assignment M :=
            λ {t : symbs.signature.S} (y : symbs.svar t) =>
              if h : s = t then
                if h ▸ x = y then
                  variant_g y
                else g' y
              else g' y
          have is_variant_g' : variant_g'.variant g' x := by
            unfold Assignment.variant
            unfold variant_g'
            aesop
          have agree_x : variant_g' x = variant_g x := by
            simp only [↓reduceDIte, ↓reduceIte, variant_g']
          specialize h variant_g' is_variant_g'
          symm at agree
          have : variant_g'.free_agree g (ℋ∀ x φ) := AgreementL1 agree is_variant_g'
          symm at this
          have : variant_g.free_agree variant_g' (ℋ∀ x φ) := AgreementL1 this is_variant_g
          symm at this
          have : variant_g'.free_agree variant_g φ := AgreementL2 this agree_x
          specialize @ih ws variant_g' variant_g this
          rw [←ih]
          exact h
    | cons φ ψs ih1 ih2 =>
        simp only [Sat.cons]
        simp only [Assignment.free_agree, FormL.varOccursFree, Bool.or_eq_true] at agree
        have ⟨agree_φ, agree_ψ⟩ : g.free_agree g' φ ∧ g.free_agree g' ψs := by
          unfold Assignment.free_agree
          aesop
        clear agree
        apply Iff.intro
        . intro ⟨h1, h2⟩
          apply And.intro
          . rw [←ih1]
            repeat assumption
          . rw [←ih2]
            repeat assumption
        . intro ⟨h1, h2⟩
          apply And.intro
          . rw [ih1]
            repeat assumption
          . rw [ih2]
            repeat assumption
    | «at» k _ ih =>
        simp only [Sat.at]
        simp only [Assignment.free_agree, FormL.varOccursFree] at agree
        rw [←Assignment.free_agree] at agree
        specialize @ih (M.VNom k) g g' agree
        exact ih

end AgreementLemma

section BarcanLemma

  lemma BarcanL1 {ψ : FormL symbs sorts} {φ : Form symbs s} {x : symbs.svar s'} (C : φ.Context ψ) (h : ψ.varOccursFree x = false) : φ.varOccursFree x = false := by
    induction C
    . exact h
    . simp only [FormL.varOccursFree, Bool.or_eq_false_iff] at h
      exact h.1
    . simp only [FormL.varOccursFree, Bool.or_eq_false_iff] at h
      apply_assumption
      exact h.2

  lemma BarcanL2 {M : Model symbs} {g g' : Assignment M} {φ : FormL symbs sorts} {x : symbs.svar s} (h1 : φ.varOccursFree x = false) (h2 : g'.variant g x) :
    g'.free_agree g φ := by
    intro t y h3
    by_cases sorts_eq : s = t
    . subst sorts_eq
      by_cases var_eq : x = y
      . subst var_eq
        rw [Bool.eq_false_iff] at h1
        contradiction
      . apply h2.1
        assumption
    . apply h2.2
      assumption

  lemma BarcanL3 {M : Model symbs} {φ : Form symbs s} {χ : Form symbs s'} {ψ : FormL symbs sorts} {C : φ.Context ψ} {C' : χ.Context ψ} {ws : WProd M.Fr.W sorts} {x : symbs.svar s''} {g g' : Assignment M} (is_var : g'.variant g x) (h1 : C.all_else_not_free x) (h2 : ¬C'.iso C) :
    (⟨M, g, ws.select C'⟩ ⊨ χ) ↔ ⟨M, g', ws.select C'⟩ ⊨ χ := by
    cases ψ with
    | cons a b =>
          cases C
          . cases C'
            . simp only [FormL.Context.iso, not_true_eq_false] at h2
            . clear h2
              simp only [FormL.Context.all_else_not_free, FormL.Context.all_else_bool,
                Bool.not_eq_eq_eq_not, Bool.not_true] at h1
              simp only [WProd.select]
              rename_i C'
              have := BarcanL1 C' h1
              have : g'.free_agree g χ := BarcanL2 this is_var
              apply Agreement
              symm
              assumption
          . cases C'
            . simp only [FormL.Context.all_else_not_free, FormL.Context.all_else_bool,
              Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
              simp only [WProd.select]
              have := h1.2
              have : g'.free_agree g χ := BarcanL2 this is_var
              apply Agreement
              symm
              assumption
            . simp only [FormL.Context.all_else_not_free, FormL.Context.all_else_bool,
              Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
              simp only [WProd.select]
              rename_i C'
              have := BarcanL1 C' h1.1
              have : g'.free_agree g χ := BarcanL2 this is_var
              apply Agreement
              symm
              assumption
    | _ =>
          cases C
          . cases C'
            . simp only [FormL.Context.iso, not_true_eq_false] at h2

  /--
    Let g be an assignment, and x a variable.
    Let "ψ" be the following list of formulas:
      φ₁, ..., φᵢ, ..., φₙ;
    Assume that x does not occur free in φⱼ if i ≠ j (C.all_else_not_free x)

    If for any x-variant g' of g there exists some φⱼ s.t.
        φⱼ is satisfied under g' at world wⱼ,
    then:
        1. Either for any x-variant g' of g, φᵢ is satisfied under g' at world wᵢ, or
        2. g satisfies some some formula in the list:
              φ₁, ..., ℋ⊥, ..., φₙ
          at its respective world.

    (Note: Substituting ℋ⊥ for φᵢ can rightfully seem like a hack. Consider specifying it like this instead:
      ∃ (C' : χ.Context ψ), ¬C'.iso C ∧ ⟨M,g,ws.select C'⟩⊨χ)
  -/
  lemma BarcanLemma {M : Model symbs} {φ : Form symbs s} {ψ : FormL symbs sorts} {C : φ.Context ψ} {ws : WProd M.Fr.W sorts} {x : symbs.svar s'} (g : Assignment M) (h : C.all_else_not_free x) :
    (∀ (g' : Assignment M), g'.variant g x → ∃ (s' : symbs.signature.S) (χ : Form symbs s') (C' : χ.Context ψ), ⟨M,g',ws.select C'⟩⊨χ) →
    (∀ (g' : Assignment M), g'.variant g x → ⟨M,g',ws.select C⟩⊨φ) ∨
    ∃ (s' : symbs.signature.S) (χ : Form symbs s') (C' : χ.Context C[ℋ⊥]), ⟨M,g,ws.select C'⟩⊨χ := by
    intro h2
    by_contra h3
    simp only [not_or, not_forall, not_exists] at h3
    have ⟨⟨g', ⟨is_variant, g'_h⟩⟩, h4⟩ := h3
    clear h3
    specialize h2 g' is_variant
    have ⟨s, ⟨χ, ⟨C', h5⟩⟩⟩ := h2
    clear h2
    specialize h4 s χ
    -- So (by g'_h) we know that g' does NOT satisfy the argument selected by context C,
    -- but (by h5)  we know that g' DOES satisfy the argument selected by context C'.
    --
    -- If C and C' are the same context (C'.iso C), this is immediately a contradiction.
    --
    -- If not, all we know is that g' does satisify some argument, other than C.
    -- But: by hypothesis h, we know that the variable x may only occur free in C, and is
    -- not free in any other argument.
    -- So g' satisfies an argument where x is not free, and since g' is an x-variant of g,
    -- by Agreement Lemma we have that g satisfies the argument selected by C'.
    -- This contradicts hypothesis h4.
    by_cases C'_iso_C : C'.iso C
    . -- Contradiction between h5 and g'_h
      have := C'.if_iso_sorts C C'_iso_C
      subst this
      have := C'.if_iso C C'_iso_C
      subst this
      rw [WProd.select_iso C'_iso_C] at h5
      exact g'_h h5
    . rw [←BarcanL3 is_variant h C'_iso_C] at h5
      have ⟨C'', C'_iso_C''⟩ := C.subst_not_iso C' (FormL.Context.iso_symm.mt C'_iso_C) (ℋ⊥)
      rw [WProd.select_iso C'_iso_C''] at h5
      specialize h4 C''
      exact h4 h5

  #print axioms BarcanLemma

end BarcanLemma

end Soundness
