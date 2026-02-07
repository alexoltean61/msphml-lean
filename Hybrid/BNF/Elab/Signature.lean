import Lean
import Hybrid.BNF.Helpers

open Lean Elab Command Term Meta

def defineSig : Name → Name → Name → Name → TermElabM Name := λ nmspace st op nom => do
  let defName : Name := .str nmspace "Sig" -- e.g., def SMC.Sig := ...
  let ty : Expr := mkAppN (mkConst ``Signature [0]) #[stringType]
  let sortsTy : Expr := setStringElemType <| mkConst st
  addAndCompile
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := ty
        value  := mkAppN (mkConst ``Signature.mk [0])
                    #[stringType, mkConst st, mkConst op, mkConst nom,
                    ]
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible
  return defName
