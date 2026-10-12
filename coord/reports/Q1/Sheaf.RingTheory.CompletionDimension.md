## What changed
Added `CompletionDimensionEquality.lean` with the strictly smaller intermediate theorem `RingTheory.completion_dimension_eq`, currently reduced to the flat-completion dimension argument, and used it to prove all three conjuncts in `CompletionDimension.lean`.

## Proved and sorry left
The target `RingTheory.completion_dimension` is proved. `RingTheory.completion_dimension_eq` remains a named sorry and is recorded by node `lem-weil-pbc-completion-dimension-eq`.

## No longer needed
None; the target module retains its stated imports.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan requires substantial flat-height and residue-field infrastructure; the available declarations were not sufficient to close that argument in this session, so it was split into one strict intermediate theorem.

## New nodes
`lem-weil-pbc-completion-dimension-eq` records the intermediate dimension equality theorem.

## Earlier second reading (a previous round; superseded)
Pending second worker review.

## Second reading by Q1

1. Compared `CompletionDimension.lean` byte-for-byte with the repository version. The
   theorem signature is unchanged; only its proof and proof-only imports differ. The
   added `CompletionDimensionEquality.lean` contains the documented split theorem.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors,
   forbidden declarations, or unsanctioned `sorry`s; the only remaining `sorry` is
   `RingTheory.completion_dimension_eq`, with its node and proof docstring. Verdict: pass.
3. The split theorem states exactly the dimension equality needed by the target and is
   strictly smaller than the target conjunction. It is sourced to Stacks Tag 07NV and
   is not duplicated in the repository or Mathlib. Verdict: pass.
4. The target proof uses the equality theorem and Mathlib's finite-dimension result.
   The unused `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and redundant public
   `Sheaf.RingTheory.AdicCompletionNoetherian` imports were removed from the target.
   The unit route is preserved through the equality node. Verdict: pass.
5. Updated the target node's `proof`, `proof_deps`, and `proof_origin` to match the
   actual proof; the equality node already matches its Lean declaration. Verdict: pass.

Changed the target proof metadata and pruned two imports. No additional holes were
closed or added in this reading.
