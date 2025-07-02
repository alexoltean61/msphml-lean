# This script generates every basic Barcan-like formula, and the Lean statement
# to check its validity / falsifiability.
#
# Every antecedent / consequent of a Barcan-like formula contains:
#   one of two binders: ℋ∀ x or ℋ∃ x
#   one of two modal operators: ℋ⟨σ⟩ or ℋ⟨σ⟩ᵈ
#
# So for each antecedent / consequent, there are 4 possibilities.
#
# This gives us 4 * 4 = 16 ways to combine them into full implications.
# But we shall also consider the converses of these implications, leaving us at
#         16 * 2 = 32 possible Barcan formulas.
#
# If one of these formulas is valid, then the contrapositive of any its instances
# is valid as well.
#
# So if you prove a formula valid, you can then factor out any other formulas that may be
# obtained from its contrapositive.
#
# TODO: Group the 32 formulas in equivalence classes by contraposition entailment.
#       But this may be faster done by hand than in code.

binders = ["ℋ∀ x", "ℋ∃ x"]
operators = ["ℋ⟨σ⟩", "ℋ⟨σ⟩ᵈ"]

antecedents = []
consequents = []

for b in binders:
    for op in operators:
        antecedents.append(f"{b} ({op} ψ)")
        consequents.append(f"{op} C[{b} φ]")

formulas = []
for lhs in antecedents:
    for rhs in consequents:
        formulas.append(f"{lhs} ⟶ {rhs}")
        formulas.append(f"{rhs} ⟶ {lhs}")

for idx, form in enumerate(formulas, start=1):
    print(f"theorem Barcan{idx}Sound {{Λ : AxiomSet symbs}} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) : \n ⊨Mod(Λ) ({form}) := sorry")
    print(f"theorem Barcan{idx}Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs), \n ¬ ⊨Mod(Λ) ({form}) := sorry\n")
