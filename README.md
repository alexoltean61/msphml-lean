# Many-Sorted Polyadic Hybrid Modal Logic in Lean

This repository contains a formalization of [[1]](https://arxiv.org/abs/1905.05036) in the [Lean 4 proof assistant](https://lean-lang.org/).

It implements a system of modal logic strong enough to define arbitrary algebraic structures and reason about their properties. This system is *polyadic* (allows modal operators with arbitrary arities), *many-sorted* (it partitions symbols based on their sorts), and *hybrid* (it allows referencing states by means of so-called *state symbols*).

In particular, our work is focused on applications to the operational semantics of programming languages. We provide a [custom DSL](Hybrid/BNF/Syntax.lean) which the user can use to define their own programming language syntax & semantics (or any other kind of algebraic structure). Feel free to check out our [examples](Hybrid/Examples/Examples.lean).

All proofs living on this branch of the repository are **formalized in their entirety** and **completely sorry-free**.

### Contents
- [Hybrid/Language/Signature.lean](Hybrid/Language/Signature.lean): Definition of signatures
- [Hybrid/Language/Form.lean](Hybrid/Language/Form.lean): Definition of formulas
- [Hybrid/Proof/Hilbert.lean](Hybrid/Proof/Hilbert.lean): Hilbert proof system
- [Hybrid/Semantics/Satisfaction.lean](Hybrid/Semantics/Satisfaction.lean): Kripke semantics
- [Hybrid/Soundness/Soundness.lean](Hybrid/Soundness/Soundness.lean): Mechanized proof of soundness theorem
- [Hybrid/Examples/SMC/Signature.lean](Hybrid/Examples/SMC/Signature.lean): Many-sorted signature for SMC machine
- [Hybrid/Examples/SMC/Axioms.lean](Hybrid/Examples/SMC/Axioms.lean): Operational semantics of SMC machine
- [Hybrid/Examples/SMC/Programs.lean](Hybrid/Examples/SMC/Programs.lean): Hoare-logic proofs for SMC machine
- [Hybrid/Examples/Protocols/Proofs.lean](Hybrid/Examples/Protocols/Proofs.lean): Protocols verification
- [Hybrid/Examples/BAN/Proofs.lean](Hybrid/Examples/BAN/Proofs.lean): BAN logic
- [Hybrid/Examples/Modal/Base/S5.lean](Hybrid/Examples/Modal/Base/S5.lean): S5 in the base modal fragment

### Building
Before you start, make sure you have [Lean installed](https://lean-lang.org/install/) in your environment.

1. Clone this repository.
2. If you wish to verify that a certain proof has been entirely formalized (e.g., `theorem Soundness`), locate it inside the project and add the line `#print axioms Soundness` at the end of the respective file.
3. From your cloned directory, run `lake build`. Note that this command may take a long time.
4. At the end, you should see the message `Build completed successfully`, along with something similar to `'Soundness' depends on axioms: [propext, Classical.choice, Quot.sound]`. You will see no `sorryAx` among listed axioms, meaning the statement is completely proved!


### References

[1]: [Operational semantics and program verification using many-sorted hybrid modal logic](https://arxiv.org/abs/1905.05036)
