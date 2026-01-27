import Hybrid.BNF.Elab.Sort
import Hybrid.BNF.Elab.Operator
import Hybrid.BNF.Elab.Nominal
import Hybrid.BNF.Elab.Signature
import Hybrid.BNF.Elab.Symbols

open Lean Elab Command Term Meta

@[command_elab language_def]
def hybrid_def_init : CommandElab
  | `(hybrid_def $name:ident := $decl:signature_decl) => do
        -- This will pass through the definition's concrete syntax tree multiple times,
        -- parsing first sorts, then operators, then nominals, then builtins.
        -- Right now the pipeline is easier to debug if it does multiple passes through the
        -- syntax.
        --
        -- 1. Compute the namespace for all declarations
        let currNamespace := (<- get).scopes.head!.currNamespace
        let defName := toString name.getId
        let declsNamespace := Name.str currNamespace defName
        -- 2. Gather & declare sorts
        let sortNames <- gatherSortNames decl
        let sortDecl <- liftTermElabM $ defineSorts declsNamespace sortNames
        -- 3. Gather, resolve & declare operators (incl. subsort ops)
        let opStx  <- gatherOps decl
        let ops    <- opStx.mapM (resolveOp declsNamespace)
        let opDecl <- liftTermElabM <| defineOps declsNamespace sortDecl ops
        -- 4.a. Gather & resolve non-builtin nominals:
        let nomStx <- gatherNoms decl
        let noms   <- nomStx.mapM (resolveNom declsNamespace)
        --  b. Gather & resolve builtin nominals:
        let bltStx <- gatherBuiltins decl
        let blts   <- bltStx.mapM (resolveBuiltin declsNamespace)
        --  c. Declare all nominals:
        let nomDecl <- liftTermElabM $ defineNoms declsNamespace sortDecl noms blts
        -- 5. Declare the signature & symbols
        let sigDecl <- liftTermElabM $ defineSig declsNamespace sortDecl opDecl nomDecl
        liftTermElabM $ defineSymb (.str .anonymous defName) sigDecl sortDecl
  | _ => throwUnsupportedSyntax
