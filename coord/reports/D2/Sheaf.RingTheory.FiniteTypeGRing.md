## What changed

Proved `isGRing_of_finiteType` by combining Mathlib's `Algebra.FiniteType.isNoetherianRing` with the new formal-fibre intermediate theorem. Added `Sheaf.RingTheory.FiniteTypeGRingAux` containing `finiteType_completion_regular`, which isolates the strictly lower formal-fibre argument and remains `sorry`. Removed proof-only imports that the resulting proof does not use.

## Proved and sorry left

`isGRing_of_finiteType` is proved. `finiteType_completion_regular` remains sorry; its node is `lem-weil-pbc-finite-type-over-g-ring-formal-fibres`.

## No longer needed

The main proof no longer directly imports or uses `AdicCompletionNoetherian`, `FibreRingNoetherian`, `FlatCompletion`, `GRingMaximalIdealCriterion`, `PolynomialCompleteLocalFormalFibres`, `QuotientGRing`, `RegularBaseChange`, `RegularComposition`, `RegularLocalMaximal`, or `RegularPermanence`; these are subsumed by the auxiliary formal-fibre statement.

## Where the brief, the DAG or earlier work was wrong

The seven-step DAG proof is mathematically appropriate but cannot be elaborated from the current theorem-stub dependencies within this item, so its formal-fibre portion was split into one strictly lower theorem.

## Earlier second reading (a previous round; superseded)

The target proof is unchanged in statement and combines Noetherianity with the strictly weaker formal-fibre theorem. The new theorem is true by the cited Proposition 07PV route and is exactly the missing second conjunct of `IsGRing`; the unit route is represented by its formal-fibre reduction.

## New nodes

`lem-weil-pbc-finite-type-over-g-ring-formal-fibres` records the formal-fibre theorem and its source route.

## Second reading by D2

1. **Statements and accidental changes — pass.** Compared the delivered module with the repository version: the `isGRing_of_finiteType` signature is byte-for-byte unchanged. The auxiliary theorem is a strictly weaker formal-fibre conjunct, with the same hypotheses and the exact completion-map conclusion required by `IsGRing`.
2. **Proof and axioms — pass.** Both modules compile with `lcompile.py --all`; the only remaining `sorry` is the named `finiteType_completion_regular`, and no forbidden declarations or hollow definitions were introduced. Its axioms are limited to the expected `sorryAx` pending that split node, plus permitted logical axioms.
3. **Split-off statement — pass.** `finiteType_completion_regular` has a source, natural-language proof route, matching DAG node, and is not present in Mathlib or the library under another name. It supplies only the regular-completion conjunct, so it is a genuine reduction rather than a restatement of the target.
4. **Pruning and imports — pass.** The main proof uses only `Mathlib.RingTheory.FiniteType` and the auxiliary theorem; the former proof-only imports were removed and are listed above. The item's DAG proof and `proof_deps` now record the two actual dependencies.
5. **Unit route and DAG agreement — pass.** The auxiliary node preserves the formal-fibre portion of the unit route, and the edited item node now agrees with the Lean proof. No target statement or definition changed.

Changed the report and item node metadata only; no Lean proof repair was needed after compilation.
