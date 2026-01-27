import Lean
import Hybrid.BNF.Helpers

open Lean Elab Command Term Meta

def defineSymb : Name → Name → Name → TermElabM Unit := λ defName sig st => do
  let ty : Expr := mkAppN (mkConst ``Symbols [0]) #[stringType]
  let sortsTy : Expr := setStringElemType <| mkConst st
  -- For now, prop and nom are always empty
  let prop : Expr := .lam `s sortsTy setEmpty .default
  let nom  : Expr := .lam `s sortsTy setEmpty .default
  -- svar is the universal string set (todo: fix)
  let svar : Expr := .lam `s sortsTy setUniv .default
  -- IMPORTANT:
  -- Proofs of countability & nominal extension are for now sorried out!
  let propCtbl ← mkSorry (.forallE `s sortsTy (mkApp (mkConst ``Encodable [0]) (setStringElemType <| mkAppN prop #[.bvar 0])) .default) false
  let nomCtbl ← mkSorry (.forallE `s sortsTy (mkApp (mkConst ``Encodable [0]) (setStringElemType <| mkAppN nom #[.bvar 0])) .default) false
  let svarCtbl ← mkSorry (.forallE `s sortsTy (mkApp (mkConst ``Denumerable [0]) (setStringElemType <| mkAppN svar #[.bvar 0])) .default) false
  let nomExt  ← mkSorry (.forallE `s sortsTy setStringType .default) false
  let hExtInf ← mkSorry (.forallE `s sortsTy (mkAppN (mkConst ``Set.CountablyInfinite [0]) #[stringType, mkApp nomExt (.bvar 0)]) .default) false
  let hExtDisj ← mkSorry (.forallE `s sortsTy (
                                  mkAppN (mkConst ``Eq [1]) #[setStringType,
                                        mkAppN (mkConst ``Inter.inter [0]) #[setStringType, mkApp (mkConst ``Set.instInter [0]) stringType, mkApp nom (.bvar 0), mkApp nomExt (.bvar 0)],
                                        mkAppN (mkConst ``EmptyCollection.emptyCollection [0]) #[setStringType, mkApp (mkConst ``Set.instEmptyCollection [0]) stringType]
                                  ]
                                )
                          .default) false
  addAndCompile
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := ty
        value  := mkAppN (mkConst ``Symbols.mk [0])
                    #[stringType, mkConst sig, prop, nom, svar,
                      propCtbl, nomCtbl, svarCtbl, nomExt, hExtInf, hExtDisj]
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible
