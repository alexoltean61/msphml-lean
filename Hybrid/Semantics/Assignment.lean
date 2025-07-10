import Hybrid.Semantics.Satisfaction

namespace Assignment

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

  lemma variant_refl {g : Assignment M} : g.variant g x := by
    unfold Assignment.variant
    aesop

  @[symm]
  lemma variant_symm {g g' : Assignment M} : g.variant g' x → g'.variant g x := by
    unfold Assignment.variant
    aesop

  @[symm]
  def free_agree_symm {M : Model symbs} {g g' : Assignment M} {φ : FormL symbs sorts} : g.free_agree g' φ → g'.free_agree g φ := by
    unfold Assignment.free_agree
    intro h1 s x h2
    symm
    apply h1
    repeat apply_assumption

  /-
  Given x and y of the same sort, and g, g' and g'' as in the diagram below, we construct h:

          g ----x---- g'
          |           |
          |           |
          y           y
          |           |
          |           |
          h ----x---- g''

  -/
  def factor_two_step_variant {M : Model symbs} {x y : symbs.svar s} {g g' g'' : Assignment M} (h1 : g'.variant g x) (h2 : g''.variant g' y) :
    Σ' h : Assignment M, h.variant g y ∧ h.variant g'' x :=
    ⟨
      λ {t : symbs.signature.S} (z : symbs.svar t) =>
        if s_eq_t : s = t then
          if s_eq_t ▸ z = y then
            g'' z
          else g z
        else g z,
        ⟨
          ⟨
            by  intros z
                simp
                intro _ h3
                subst h3
                contradiction,
            by  intro t z h3
                simp [h3]
          ⟩,
          ⟨
            by  intros t
                simp
                intro h3 h4
                rw [←not_ne_iff, not_not] at h3 h4
                rw [ne_comm] at h4
                simp [h2.1 t h4, h1.1 t h3],
            by  intro t z h3
                simp [h3]
                simp [h2.2 z h3, h1.2 z h3]
          ⟩
        ⟩
    ⟩

  /-
    If x and y have different sorts, the construction above can't be made (try to define h, you'll see it can't
    be simultaneously a variant of g and a variant of g'').

    But we can refactor g' and g'' by, in essence, reversing their order, while maintaing the same final result:
  -/
  def factor_two_step_variant_diff_sorts {M : Model symbs} {x : symbs.svar s} {y : symbs.svar u} {g g' g'' : Assignment M} (h1 : g'.variant g x) (h2 : g''.variant g' y) (hneq_sorts : ¬s = u) :
    Σ' h' h'' : Assignment M, h'.variant g y ∧ h''.variant h' x ∧ h''.equal g'' :=
    let h' : Assignment M :=
      λ {t : symbs.signature.S} (z : symbs.svar t) =>
        if s_eq_t : t = u then
          if s_eq_t ▸ z = y then
            g'' z
          else g z
        else g z
    let h'' :=
      λ {t : symbs.signature.S} (z : symbs.svar t) =>
        if s_eq_t : t = s then
          if s_eq_t ▸ z = x then
            g' z
          else h' z
        else h' z
    ⟨h', ⟨h'',
      ⟨by unfold variant h'; aesop,
      ⟨by unfold variant h'; aesop,
      by
        intro t z
        simp
        unfold variant at h1 h2
        have ⟨a, b⟩ := h1
        have ⟨c, d⟩ := h2
        clear h1 h2
        simp only [ne_eq] at a b c d
        by_cases h_sort : s = t
        . subst h_sort
          by_cases h_var : z = x
          . subst h_var
            . by_cases h_sort : u = s
              . subst h_sort
                contradiction
              . simp [h'']
                aesop
          . simp [h'', h', h_var, hneq_sorts]
            have sorts_symm : ¬u = s := by intro; apply hneq_sorts; aesop
            have var_symm : ¬x = z := by intro; apply h_var; aesop
            specialize d z sorts_symm
            rw [d]
            specialize a z var_symm
            rw [a]
        . by_cases h_sort : u = t
          . subst h_sort
            by_cases h_var : y = z
            . simp [h'']
              symm; aesop
            . simp [h'']
              symm; aesop
          . simp [h'']
            symm; aesop
        ⟩
      ⟩
      ⟩
    ⟩

end Assignment
