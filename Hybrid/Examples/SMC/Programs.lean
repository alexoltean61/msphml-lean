import Hybrid.Examples.SMC.Lemmas

open SMC
open Proof

def assgnNat (s : SMCForm Var) (v : SMCForm Nat):
  SMCProof _
    (⟨vs, mem⟩ ⟶ [c(s ::= v)] ⟨vs, set(mem, s, v)⟩) := by
    apply propagateDAsgn
    apply composition
    case φ₁ => exact ⟨v ⬝ vs, mem⟩
    . exact aint
    . exact aasgn

def swapPgm (x y aux : SMCForm Var) : SMCForm Stmt :=
  aux ::= x;
  x   ::= y;
  y   ::= aux

def swapCorrect
  (neq1 : y ≠ x)
  (neq2 : y ≠ aux)
  : SMCProof _
    (⟨vs, set(set(mem, y, yn), x, xn)⟩ ⟶ [c(swapPgm x y aux)] ⟨vs, set(set(set(mem, x, yn), aux, xn), y, xn)⟩) := by
  apply propagateSeq
  apply composition
  . apply assgnVar
    exact aid
  . apply propagateSeq
    apply composition
    . apply assgnVar
      . apply propagateMemL (bubble3Mem neq1 neq2) ?transition -- HERE
        . exact yn
        . apply propagateMemR (bubble3Mem neq1 neq2)           -- HERE
          apply aid
    . apply @propagateMemL _ _ _ _ (set(set(set(mem, y, yn), x, yn), aux, xn))
      . -- HERE
        admit
      . apply @propagateMemR _ _ _ _ (set(set(set(set(mem, y, yn), x, yn), aux, xn), y, xn))
        . -- HERE
          admit
        . apply assgnVar
          exact aid

def sumPgm (s i n : CtNoms Var)
  : SMCForm Stmt :=
  s ::= 0;
  i ::= 0;
  while (++i <= n) do:
    s ::= s + i
  od

def sumCorrect (vs : SMCForm ValStack)
        (mem : SMCForm Mem)
        (s i n : CtNoms Var)
        (vn : ℕ) :
    SMCProof _
      (⟨vs, set(mem, n, vn)⟩ ⟶ [c(sumPgm s i n)] ⟨vs, set(set(set(mem, n, vn), s, (vn *Nat (vn *Nat (vn +Nat 1)) /Nat 2)), i, vn +Nat 1)⟩) := by
    -- Let xvi be a variable that does not occur free in vs or mem:
    let freeIn : FormLList SMC := [⟨_, vs⟩, ⟨_, mem⟩]
    let xvi  : SMC.svar Nat  := freeIn.freshVar Nat
    let vi   := ℋVar xvi
    have freeVs  : vs.occurs_free xvi = false := FormL.freshVarListIsFresh ⟨_, vs⟩ (by simp [freeIn])
    have freeMem : mem.occurs_free xvi = false := FormL.freshVarListIsFresh ⟨_, mem⟩ (by simp [freeIn])
    --
    let xB   : SMCForm Bool := vi <=Nat vn
    let xmem : SMCForm Mem  := set(set(set(mem, s, (vi *Nat (vi -Nat 1)) /Nat 2), i, vi ⋀ ℋ@ true (vi <=Nat (vn +Nat 1))), n, vn)
    let init : ⟨xB ⬝ vs, xmem⟩.Instance := ⟨[⟨_, xvi, (1:ℕ)⟩]⟩
    apply propagateSeq
    apply composition
    . apply assgnNat
    . apply propagateSeq
      apply composition
      . apply assgnNat
      . apply weakeningPost
        . apply iteration (by simp) (by simp) xB vs xmem init
          . apply propagateDLeq
            apply composition
            . apply app
            . dsimp only [Nat.add_eq, Nat.reduceAdd]
              apply composition
              . have pfMem : SMCProof _
                  (set(set(set(mem, n, vn), s, (0:ℕ)), i, (0 +Nat 1)) ←→ set(set(set(mem, s, (0:ℕ)), i, (1:ℕ)), n, vn))
                    := sorry -- TODO! Note that this permutes the memory AND computes arithmetic 0 +Nat 1
                let pfStack : SMCProof _
                  (((0 +Nat 1) ⬝ vs) ←→ ((1:ℕ) ⬝ vs)) := sorry -- TODO! (arithmetic)
                apply propagateMemL pfMem
                apply propagateStackL pfStack
                apply aid
              . simp [
                  OfNat.ofNat,
                  FormL.not_free_nom_subst freeVs,
                  FormL.not_free_nom_subst freeMem,
                  xB, vi, xmem, init
                ]
                apply propagateNLeq
                -- Auxiliary arithmetic proofs (TODO!)
                let pf1 : SMCProof _ (1 -Nat 1 ←→ 0) := sorry
                let pf2 : SMCProof _ (1 *Nat (1 -Nat 1) ←→ 1 *Nat 0) := sorry
                let pf3 : SMCProof _ (1 *Nat 0 ←→ 0) := sorry
                let pf4 : SMCProof _ ((1 *Nat ((1 -Nat 1))) /Nat 2 ←→ 0 /Nat 2) := sorry
                let pf5 : SMCProof _ (0 /Nat 2 ←→ 0) := sorry
                let pf6 : SMCProof _ ((1 *Nat ((1 -Nat 1))) /Nat 2 ←→ 0) := sorry
                let pfMem1 : SMCProof _
                  (set(set(set(mem, s, ((1 *Nat ((1 -Nat 1))) /Nat 2)), i, (1:ℕ) ⋀ ℋ@ true (1 <=Nat (vn +Nat 1))), n, vn)
                    ←→
                  set(set(set(mem, s, (0:ℕ)), i, (1:ℕ) ⋀ ℋ@ true (1 <=Nat (vn +Nat 1))), n, vn)) := sorry
                -- Should be provable that, for all x, |- ℋ@ true (1 <=Nat x + 1)
                let pfMem2 : SMCProof _
                  (set(set(set(mem, s, (0:ℕ)), i, (1:ℕ)), n, vn)
                    ←→
                  set(set(set(mem, s, (0:ℕ)), i, (1:ℕ) ⋀ ℋ@ true (1 <=Nat (vn +Nat 1))), n, vn)) := sorry
                ----------------
                apply propagateMemR pfMem1
                apply propagateMemL pfMem2
                apply aleqNat
          . intro preBody
            -- preBody is the concrete configuration which holds before executing the loop.
            -- It's an instance of the invariant,
            -- i.e., it maps the symbolic variable xvi to some nominal preVi.
            -- Need to provide another instance of the invariant, and show that it will hold
            -- after the loop;
            -- i.e., find a different mapping of xvi to some concrete value.
            let preVi := preBody.inst.valueOf xvi
            apply Sigma.mk ?_invInst ?_invPf
            . -- Here we construct the post-loop invariant instance
              -- Clearly, xvi should be mapped to preVi + 1:
              let postVi : ℕ := Encodable.encode preVi + 1
              exact ⟨[⟨_, xvi, postVi⟩]⟩
            . apply composition
              . apply propagateDAsgn
                apply composition
                . simp
                  apply propagateDPlus
                  apply composition
                  . apply helperInsertAndL
                    let pfMem :
                      SMCProof _
                        (set(set(set(preBody.inst.apply mem, s, ℋ⟨nat2Val⟩(ℋ⟨DivNat⟩(ℋ⟨MulNat⟩(preBody.inst.apply vi, (preBody.inst.apply vi -Nat 1)), (2:ℕ)))), i, ℋ⟨nat2Val⟩(preBody.inst.apply vi) ⋀ ℋ@ (true)(ℋ⟨LeqNat⟩(preBody.inst.apply vi, ℋ⟨PlusNat⟩(ℋNom ↑↑vn, (1:ℕ))))), n, ℋ⟨nat2Val⟩(vn))
                          ←→
                        set(set(set(mem, i, ℋ⟨nat2Val⟩(preBody.inst.apply vi) ⋀ ℋ@ (true)(ℋ⟨LeqNat⟩(preBody.inst.apply vi, ℋ⟨PlusNat⟩(ℋNom ↑↑vn, (1:ℕ))))), n, ℋ⟨nat2Val⟩(vn)), s, ℋ⟨nat2Val⟩(ℋ⟨DivNat⟩(ℋ⟨MulNat⟩(preBody.inst.apply vi, ℋ⟨MinusNat⟩(preBody.inst.apply vi, (1:ℕ))), (2:ℕ)))))
                        := sorry
                    simp [xmem, OfNat.ofNat]
                    apply propagateMemL pfMem
                    apply aid
                  . apply composition
                    . let pfMem :
                        SMCProof _
                          (set(set(set(mem, i, ↑(preBody.inst.apply vi) ⋀ ℋ@ (true)(preBody.inst.apply vi <=Nat (vn +Nat 1))), n, vn), s, (preBody.inst.apply vi *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2)
                            ⟶
                          set(set(set(mem, n, vn), s, (preBody.inst.apply vi *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2), i, ↑(preBody.inst.apply vi) ))
                          := sorry   -- TODO! (Here you are also getting rid of @true ... inside i, so this is only a left-to-right implication)
                          -- wrong to get rid of @true ...
                      apply propagateMemL' pfMem
                      apply aid
                    . apply aplus
                . apply aasgn
              . apply propagateDLeq
                apply composition
                . let pfMem :
                        SMCProof _
                          (set(set(set(set(mem, n, vn), s, (preBody.inst.apply vi *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2), i, ↑(preBody.inst.apply vi)), s, ((((preBody.inst.apply vi) *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2) +Nat preBody.inst.apply vi))
                            ←→
                          set(set(set(set(mem, n, vn), s, (preBody.inst.apply vi *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2), s, ((((preBody.inst.apply vi) *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2) +Nat preBody.inst.apply vi)), i, ↑(preBody.inst.apply vi)))
                          := sorry   -- TODO!
                  apply propagateMemL pfMem
                  apply app
                . apply composition
                  . let pfMem :
                        SMCProof _
                          (set(set(set(set(mem, n, vn), s, (preBody.inst.apply vi *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2), s, ((((preBody.inst.apply vi) *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2) +Nat preBody.inst.apply vi)), i, ↑(preBody.inst.apply vi) +Nat 1)
                            ←→
                          set(set(set(set(mem, s, (preBody.inst.apply vi *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2), s, ((((preBody.inst.apply vi) *Nat (preBody.inst.apply vi -Nat 1)) /Nat 2) +Nat preBody.inst.apply vi)), i, ↑(preBody.inst.apply vi) +Nat 1), n, vn))
                          := sorry   -- TODO!
                    apply propagateMemL pfMem
                    apply aid
                  . conv =>
                      rhs ; rhs
                      simp [
                        OfNat.ofNat,
                        FormL.not_free_nom_subst freeVs,
                        FormL.not_free_nom_subst freeMem,
                        xB, vi, xmem, init
                      ]
                    ----------------------
                    let postVi : SMC.nominal Nat := ((Encodable.encode preVi + 1):ℕ)
                    have strongUnsoundAssumption : (ℋNom postVi) = (preBody.inst.apply vi +Nat 1) := sorry
                    rw [strongUnsoundAssumption]
                    ----------------------
                    have strongUnsoundAssumption2 : ℋ⟨nat2Val⟩(FormL.Instantiation.apply vi preBody.inst +Nat 1) ⋀
                    ℋ@
                      (↑↑true)(ℋ⟨LeqNat⟩(FormL.Instantiation.apply vi preBody.inst +Nat 1,
                          ℋ⟨PlusNat⟩(ℋNom ↑↑vn, ℋNom (1:ℕ)))) = ℋ⟨nat2Val⟩(FormL.Instantiation.apply vi preBody.inst +Nat 1) := sorry
                    rw [strongUnsoundAssumption2]
                    -----------------------
                    have := aleq (FormL.Instantiation.apply vi preBody.inst +Nat 1) vn (FormL.Instantiation.apply vs preBody.inst) (set(set(set(set(mem, ↑↑s, ↑((FormL.Instantiation.apply vi preBody.inst *Nat FormL.Instantiation.apply vi preBody.inst -Nat 1) /Nat  2)), ↑↑s, ↑(((FormL.Instantiation.apply vi preBody.inst *Nat FormL.Instantiation.apply vi preBody.inst -Nat 1) /Nat 2) +Nat FormL.Instantiation.apply vi preBody.inst)), ↑↑i, ↑(FormL.Instantiation.apply vi preBody.inst +Nat 1)), ↑↑n, ↑↑↑↑vn))
                    convert aleq
                    admit
        . have eqFV : ⟨↑xB ⬝ vs, xmem⟩.FV = (⟨vs, xmem⟩ ⋀ ℋ@ ↑↑false↑xB).FV := sorry -- TODO!
          rw [eqFV]
          apply mp (existElimPf _)
          . apply genIterated
            unfold xmem ; unfold xB
            admit
          . -- Oops! vs may not be closed!
            admit

def effectfulIf (i : SMCForm Var): SMCForm Stmt :=
  if (++i <= 1) then
    i ::= 2
  else
    i ::= 3
  endif

def ifCorr (i : SMCForm Var):
    SMCProof _
      (⟨vs, set(mem, i, (0 : ℕ))⟩ ⟶ [c(effectfulIf i)] ⟨vs, set(mem, i, (2 : ℕ))⟩) := by
    apply conditional
    . have test := @app vs mem i 0
      simp at test

      admit
    repeat admit
