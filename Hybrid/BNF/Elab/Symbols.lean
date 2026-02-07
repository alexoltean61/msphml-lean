import Lean
import Hybrid.BNF.Helpers

open Lean Elab Command Term Meta

def defineSymb : Syntax → Name → Name → Name → TermElabM Unit := λ stx defName sig st => do
  let ty : Expr := mkAppN (mkConst ``Symbols [0]) #[stringType]
  let sortsTy : Expr := setStringElemType <| mkConst st
  -- For now, prop and nom are always empty
  let prop : Expr := .lam `s sortsTy setEmpty .default
  let nom  : Expr := .lam `s sortsTy setEmpty .default
  -- svar is the universal string set (todo: fix)
  let svar : Expr := .lam `s sortsTy setUniv .default
  -- IMPORTANT:
  -- Proofs of countability are for now sorried out!
  let svarCtbl ← mkSorry (.forallE `s sortsTy (mkApp (mkConst ``Denumerable [0]) (setStringElemType <| mkAppN svar #[.bvar 0])) .default) false
  addAndCompile
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := ty
        value  := mkAppN (mkConst ``Symbols.mk [0])
                    #[stringType, mkConst sig, prop, nom, svar, svarCtbl]
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible
  -- Add hover info to syntax:
  discard <| addTermInfo stx (mkConst defName []) (isBinder := true)
