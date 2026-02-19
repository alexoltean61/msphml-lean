import Lean
import Hybrid.BNF.Helpers

open Lean Elab Command Term Meta

abbrev universalStringSet : Set String := Set.univ
abbrev univStringSetInh : Inhabited universalStringSet :=
  ⟨"p", by simp⟩

def defineSymb : Syntax → Name → Name → Name → TermElabM Unit := λ stx defName sig st => do
  let ty : Expr := mkAppN (mkConst ``Symbols [0]) #[stringType]
  let sortsTy : Expr := setStringElemType <| mkConst st
  -- For now, svar and nom are always empty
  let svar : Expr := .lam `s sortsTy (.const ``universalStringSet []) .default
  let nom  : Expr := .lam `s sortsTy setEmpty .default
  -- prop is the universal string set (todo: fix)
  let prop : Expr := .lam `s sortsTy (.const ``universalStringSet []) .default
  let propInh : Expr := .lam `s sortsTy (.const ``univStringSetInh []) .default
  addAndCompile
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := ty
        value  := mkAppN (mkConst ``Symbols.mk [0])
                    #[stringType, mkConst sig, prop, nom, svar, propInh]
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible
  -- Add hover info to syntax:
  discard <| addTermInfo stx (mkConst defName []) (isBinder := true)
