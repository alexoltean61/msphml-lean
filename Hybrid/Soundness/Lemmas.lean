
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

section SubstitutionLemma

  -- Extremely annoying that this had to be handled so.
  -- It is due to Assignments being many-sorted that plain functional extensionality doesn't work.
  lemma SubstitutionL0 {M : Model symbs} {g g' : Assignment M} {φ : FormL symbs sorts} {w : WProd M.Fr.W sorts} (h : g.equal g'): (⟨M, g, w⟩ ⊨ φ) ↔ ⟨M, g', w⟩ ⊨ φ := by
  induction φ generalizing g g' with
  | svar x =>
      specialize h x
      simp [Sat.svar, h]
  | bind y _ ih =>
      rename_i t _ _
      simp only [Sat.forall]
      apply Iff.intro
      repeat {
        intro h2 g'' g''_var
        unfold Assignment.equal at h
        let g''' : Assignment M :=
          λ {u : symbs.signature.S} (z : symbs.svar u) =>
            if h : t = u then
              if h ▸ y = z then
                g'' z
              else g' z
            else g' z
        rw [ih]
        . apply h2 g'''
          unfold g''' Assignment.variant
          apply And.intro
          repeat {
            intros
            aesop
          }
        . unfold Assignment.equal
          intro u z
          by_cases h3 : t = u
          . subst h3
            by_cases h3 : y = z
            . subst h3
              simp [g''']
            . simp [g''_var.1, h3, g''', h]
          . simp [g''_var.2, h3, g''', h]
      }
  | appl _ _ ih =>
      simp only [Sat.appl]
      conv =>
        lhs ; rhs ; ext; lhs
        rw [ih h]
  | or _ _ ih1 ih2 =>
      simp only [Sat.or]
      rw [ih1 h, ih2 h]
  | cons _ _ ih1 ih2 =>
      simp only [Sat.cons]
      rw [ih1 h, ih2 h]
  | neg _ ih =>
      simp only [Sat.neg]
      rw [ih h]
  | «at» _ _ ih =>
      simp only [Sat.at]
      rw [ih h]
  | _ =>
      simp

  /--
    Following up, we have two lemmas that look almost identical, but are actually not:
      SubstitutionL1 and SubstitutionL2.

    The difference is in the way that the (x,y)  and   z variables are made to differ:
      they either have different sorts (L1),
      or they are the same sort but they are not identical (L2).

    Based on this, we require different construction methods for the assignment variants:
      either Assignment.factor_two_step_variant_diff_sorts, or
             Assignment.factor_two_step_variant

    I don't think the two cases can be unified.
  -/
  lemma SubstitutionL1 {M : Model symbs} {x y : symbs.svarType t} {z : symbs.svarType u}
   {g g' : Assignment M} {φ : Form symbs s} {ws : M.Fr.W s}
    {ih : ∀ {g g' : Assignment M} {ws : WProd M.Fr.W ([s])},
        FormL.varSubstableFor y x φ = true →
          g'.variant g x → g' x = g y → ((⟨M,g,ws⟩⊨φ[y//x]) ↔ ⟨M,g',ws⟩⊨φ)}
    {hneq_sorts : ¬t = u}
    {h1 : FormL.varSubstableFor y x φ = true}
    {h2 : g'.variant g x}
    {h3 : g' x = g y}:
      (⟨M,g,ws⟩⊨ℋ∀ z φ[y//x]) ↔ ⟨M,g',ws⟩⊨ℋ∀ z φ := by

    apply Iff.intro
    . intro h4 g'' g''_variant_g'
      have g''_agree_g' : g'' x = g' x := by
                apply g''_variant_g'.2
                simp [ne_eq, ne_comm, hneq_sorts]
      have ⟨h', ⟨h'', ⟨h'_var, ⟨h''_var, equal⟩⟩⟩⟩ := Assignment.factor_two_step_variant_diff_sorts h2 g''_variant_g' hneq_sorts
      rw [←(SubstitutionL0 equal)]
      rw [←ih]
      . apply h4
        exact h'_var
      . exact h1
      . exact h''_var
      . simp [equal x, g''_agree_g', h3]
        symm
        apply h'_var.2
        simp [ne_comm, hneq_sorts]
    . intro h4 g'' g''_variant_g
      have g''_agree_g : g'' y = g y := by
                apply g''_variant_g.2
                simp [ne_eq, ne_comm, hneq_sorts]
      symm at h2
      have ⟨h', ⟨h'', ⟨h'_var, ⟨h''_var, equal⟩⟩⟩⟩ := Assignment.factor_two_step_variant_diff_sorts h2 g''_variant_g hneq_sorts
      rw [←(SubstitutionL0 equal)]
      rw [ih]
      . apply h4
        exact h'_var
      . exact h1
      . symm
        exact h''_var
      . simp [equal y, g''_agree_g, ←h3]
        apply h'_var.2
        simp [ne_comm, hneq_sorts]

  lemma SubstitutionL2 {M : Model symbs} {x y z : symbs.svarType t}
   {g g' : Assignment M} {φ : Form symbs s} {ws : M.Fr.W s}
    {ih : ∀ {g g' : Assignment M} {ws : WProd M.Fr.W ([s])},
        FormL.varSubstableFor y x φ = true →
          g'.variant g x → g' x = g y → ((⟨M,g,ws⟩⊨φ[y//x]) ↔ ⟨M,g',ws⟩⊨φ)}
    {hneq_y : ¬y = z}
    {hneq_x : ¬x = z}
    {h1 : FormL.varSubstableFor y x φ = true}
    {h2 : g'.variant g x}
    {h3 : g' x = g y}:
      (⟨M,g,ws⟩⊨ℋ∀ z φ[y//x]) ↔ ⟨M,g',ws⟩⊨ℋ∀ z φ := by

    apply Iff.intro
    . intro h4 g'' g''_variant_g'
      have ⟨h, ⟨h_variant_g, h_variant_g''⟩⟩ := Assignment.factor_two_step_variant h2 g''_variant_g'
      have g''_agree_g' : g'' x = g' x := by
                apply g''_variant_g'.1
                simp [ne_eq, ne_comm, hneq_x]
      specialize h4 h h_variant_g
      rw [←ih]
      . exact h4
      . exact h1
      . symm
        exact h_variant_g''
      . rw [g''_agree_g', h3]
        symm
        apply h_variant_g.1
        simp [ne_comm, hneq_y]
    . intro h4 g'' g''_variant_g
      have g''_agree_g' : g'' y = g y := by
                apply g''_variant_g.1
                simp [ne_eq, ne_comm, hneq_y]
      symm at h2
      have ⟨h, ⟨h_variant_g', h_variant_g''⟩⟩ := Assignment.factor_two_step_variant h2 g''_variant_g
      specialize h4 h h_variant_g'
      rw [ih]
      . exact h4
      . exact h1
      . exact h_variant_g''
      . rw [g''_agree_g', ←h3]
        apply h_variant_g'.1
        simp [ne_comm, hneq_x]

  lemma Substitution {M : Model symbs} {g g' : Assignment M} {φ : FormL symbs sorts} {ws : WProd M.Fr.W sorts} {x y : symbs.svarType t} (h1 : φ.varSubstableFor y x) (h2 : g'.variant g x) (h3 : g' x = g y) :
    (⟨M, g, ws⟩ ⊨ φ[y // x]) ↔ ⟨M, g', ws⟩ ⊨ φ := by
    induction φ generalizing g g' with
    | bind z φ ih =>
        -- ⟨M, g, ws⟩ ⊨ (∀ z φ)[y // x]   iff   ⟨M, g', ws⟩ ⊨ ∀ z φ
        rename_i t' _
        by_cases x_free : φ.varOccursFree x
        . -- Case 1: x is free in φ, so substitution *may* happen
          by_cases eq_sorts : t = t'
          . subst eq_sorts
            by_cases eq_form_1 : y = z
            . subst eq_form_1
              -- If y = z, then by h1 x must not be free in φ
              -- This contradicts the x_free assumption
              simp [FormL.varSubstableFor] at h1
              rw [h1] at x_free
              contradiction
            . by_cases eq_form_2 : x = z
              . -- In this case we have:
                --   (∀ x φ)[y // x], which is the same as ∀ x φ.
                -- No substitution happens: this is basically the same
                -- as case 2 below
                subst eq_form_2
                simp only [FormL.subst_var_bind]
                apply Agreement
                apply BarcanL2
                . apply FormL.notFreeBound'
                . symm
                  exact h2
              . -- In this case all of x, y and z are distinct, so we have to prove:
                --  ⟨M, g, ws⟩ ⊨ (∀ z φ[y // x])   iff   ⟨M, g', ws⟩ ⊨ ∀ z (φ[y // x])
                -- Given that x is free for y in φ.
                simp only [FormL.varSubstableFor, x_free, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, ↓reduceDIte, Bool.and_eq_true, bne_iff_ne, ne_eq, eq_form_1,
                  not_false_eq_true, and_true] at h1
                simp only [eq_form_2, not_false_eq_true, FormL.subst_var_bind_neq_vars]
                apply SubstitutionL2
                repeat assumption
          . -- Same as just above: all are distinct, same conditions. Same proof procedure
            simp only [FormL.varSubstableFor, x_free, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            eq_sorts, ↓reduceDIte, Bool.and_true] at h1
            simp only [eq_sorts, not_false_eq_true, FormL.subst_var_bind_neq_sorts]
            apply SubstitutionL1
            repeat assumption
        . -- Case 2: x is not free in φ, so no substitution happens
          rw [←ne_eq, ←Bool.eq_false_iff] at x_free
          rw [FormL.notFreeVarSubst $ FormL.notFreeBound x_free]
          apply Agreement
          apply BarcanL2
          . exact FormL.notFreeBound x_free
          . symm
            exact h2
    | svar z =>
        rename_i t'
        by_cases eq_sorts : t = t'
        . subst eq_sorts
          by_cases eq_form : x = z
          . subst eq_form
            simp only [Term.subst, FormL.varSubst, ↓reduceDIte, ↓reduceIte, Sat.svar]
            rw [h3]
          . rw [←ne_eq] at eq_form
            simp only [Term.subst, FormL.varSubst, ↓reduceDIte, eq_form, ↓reduceIte, Sat.svar]
            rw [h2.1 z eq_form]
        . rw [←ne_eq] at eq_sorts
          simp only [Term.subst, FormL.varSubst, eq_sorts, ↓reduceDIte, Sat.svar]
          rw [h2.2 z eq_sorts]
    | appl σ ψ ih =>
        simp only [FormL.varSubstableFor] at h1
        simp only [FormL.subst_var_appl, Sat.appl]
        conv =>
          lhs ; rhs ; ext w' ; lhs
          rw [@ih g g' w' h1 h2 h3]
    | or φ ψ ih1 ih2 =>
        simp only [FormL.varSubstableFor, Bool.and_eq_true] at h1
        have ⟨h1l, h1r⟩ := h1
        clear h1
        simp only [FormL.subst_var_or, Sat.or]
        rw [ih1, ih2]
        repeat assumption
    | neg φ ih =>
        simp only [FormL.varSubstableFor] at h1
        simp only [FormL.subst_var_neg, Sat.neg]
        rw [ih]
        repeat assumption
    | cons φ ψs ih1 ih2 =>
        simp only [FormL.varSubstableFor, Bool.and_eq_true] at h1
        have ⟨h1l, h1r⟩ := h1
        clear h1
        simp only [FormL.subst_var_cons, Sat.cons]
        rw [ih1, ih2]
        repeat assumption
    | «at» k _ ih =>
        simp only [FormL.varSubstableFor] at h1
        simp only [FormL.subst_var_at, Sat.at]
        rw [ih]
        repeat assumption
    | _ => simp only [Term.subst, FormL.varSubst, Sat.nom, Sat.prop]

end SubstitutionLemma

end Soundness
