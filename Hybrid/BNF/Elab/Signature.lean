import Lean
import Hybrid.BNF.Helpers

open Lean Elab Command Term Meta

def defineSig : Name → Name → Name → Name → TermElabM Name := λ nmspace st op nom => do
  let defName : Name := .str nmspace "Sig" -- e.g., def SMC.Sig := ...
  let ty : Expr := mkAppN (mkConst ``Signature [0]) #[stringType]
  let sortsTy : Expr := setStringElemType <| mkConst st
  -- IMPORTANT:
  -- Proofs of countability / inhabitance are for now sorried out!
  let sortsCtbl ← mkSorry (mkApp (mkConst ``Encodable [0]) <| sortsTy) false
  let opsCtbl ← mkSorry (.forallE `dom (listType sortsTy) (.forallE `rng sortsTy (mkApp (mkConst ``Encodable [0]) (setStringElemType <| mkAppN (mkConst op) #[.bvar 1, .bvar 0])) .default) .default) false
  let nomCtbl ← mkSorry (.forallE `s sortsTy (mkApp (mkConst ``Encodable [0]) (setStringElemType <| mkAppN (mkConst nom) #[.bvar 0])) .default) false
  let sNonEmpty ← mkSorry (mkAppN (mkConst ``Inhabited [1]) #[sortsTy]) false
  let nNonEmpty ← mkSorry (.forallE `s sortsTy (mkAppN (mkConst ``Inhabited [1]) #[setStringElemType <| mkAppN (mkConst nom) #[.bvar 0] ]) .default) false
  addAndCompile -- TODO: ensure no declaration with the same name exists in the namespace!
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := ty
        value  := mkAppN (mkConst ``Signature.mk [0])
                    #[stringType, mkConst st, mkConst op, mkConst nom,
                      sortsCtbl, opsCtbl, nomCtbl, sNonEmpty, nNonEmpty
                    ]
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible
  return defName
