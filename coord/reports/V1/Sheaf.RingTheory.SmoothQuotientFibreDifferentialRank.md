## What changed

Added the proof-only import `Sheaf.RingTheory.SmoothQuotientFibreFinrankAdd` and proved
`Algebra.smooth_quotient_fibre_differential_rank` from its additive finrank identity by
natural-number arithmetic. Added the intermediate module and node
`lem-weil-pbc-smooth-quotient-fibre-finrank-add`.

## Proved and sorry left

The target declaration `Algebra.smooth_quotient_fibre_differential_rank` is proved.
The new declaration `Algebra.smooth_quotient_fibre_finrank_add` remains `sorry`; it is a
strictly smaller additive rank identity and has its own node.

## No longer needed

Removed the proof-only imports `Sheaf.RingTheory.PresentationLocalizedConormalSplit`,
`Mathlib.RingTheory.Kaehler.TensorProduct`, and `Mathlib.LinearAlgebra.TensorProduct.Prod`
from the target module; the target proof uses only the new intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The original node proof plan expands the full split-conormal and base-change argument.
This delivery factors that argument into the additive rank identity, leaving only the
necessary arithmetic at the target.

## New nodes

`lem-weil-pbc-smooth-quotient-fibre-finrank-add` records the additive rank identity used
by the target. Its module is `lean/Sheaf/RingTheory/SmoothQuotientFibreFinrankAdd.lean`.

## Earlier second reading (a previous round; superseded)

The target proof applies the additive identity with exactly matching parameters and
uses `omega` to derive both natural-number conclusions. The new statement is a strict
intermediate equality, with the same modules and no weakened target assumptions; the
unit route is represented by its split-conormal and base-change proof description.

## Second reading by V1

1. **Visible declarations:** Compared the delivered target module with the repository version. The theorem signature and docstring are unchanged; only proof-only imports and the proof body changed. The new intermediate module and node are explicitly declared in this delivery.
2. **Proof validity:** Both sandbox modules compile cleanly with `lcompile.py`. The target has no `sorry`; the only remaining `sorry` is the named intermediate theorem `Algebra.smooth_quotient_fibre_finrank_add`, with its node and proof docstring. No forbidden declarations or hollow definitions occur.
3. **Split statement:** The additive identity is true by the stated split-conormal and differential-base-change route, and is strictly weaker/smaller than the target's conjunction (it supplies exactly the arithmetic premise used by the target). It is not duplicated in the existing library.
4. **Pruning and route:** The target now uses only the additive identity and arithmetic. The removed imports are proof-only and are listed above; the unit's split-conormal/base-change route is retained in the intermediate node's proof plan.
5. **DAG agreement:** The target node's proof and dependencies match the Lean proof, and the new node records its statement, source, proof, dependencies, searches, and Lean declaration consistently.

I changed only this report section after review; no Lean declarations or node statements required repair.
