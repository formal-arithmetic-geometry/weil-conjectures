## What changed

Restored and proved `CategoryTheory.module_abelian_evaluation_comparison_general` in
`Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`. Its existence, degree-zero
normalization and arbitrary-resolution-lift formula use the module's existing
`exact_comp_comparison`, `exact_comp_comparison_zero` and
`exact_comp_comparison_formula`, with the existing general-site injective acyclicity
helper. Uniqueness follows by choosing standard injective resolutions and one
`descOfQuasiIso` lift, applying both lift formulas, and cancelling the final
resolution isomorphism. Updated the owning node's proof with this uniqueness step.

The original Precoverage theorem, all signatures, definitions and imports are retained.
The source read was Stacks `sites-cohomology.tex`, Tag 03FD,
`lemma-cohomology-modules-abelian-agree`, including its second displayed equality
and injective-acyclicity argument. The unit's route is unchanged.

Searches: LeanFinder for uniqueness of derived-evaluation comparisons returned
injective-resolution naturality lemmas; Loogle found `CategoryTheory.Iso.ext`;
Mathlib grep for `descOfQuasiIso_commutes|NatIso.ext` returned no matches through
msearch. Direct source search and the existing helpers provided the lift API.
No new mathematical lemma was required. The revised item compiled cleanly through
`lcompile.py` in 31.0 seconds; no warnings or errors were reported.

## Proved and sorry left

Current-base hole count: 0 before, 0 after; closed 0 holes and added 0 holes.
Restored the fully proved `CategoryTheory.module_abelian_evaluation_comparison_general`
(node `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`), which the
rollback removed entirely. The returned delivery had closed its former single
hole, but that is not a current-base hole closure. Split off 0 statements.
No `sorry` remains in the item module.

## No longer needed

None. No imports, nodes or modules are pruned. The existing proof dependency
imports remain used by the retained helper proofs and the general-site argument.

## Where the brief, the DAG or earlier work was wrong

The DAG already described the comparison construction and normalization but did
not explicitly describe uniqueness for its additional general-site interface.
The added elementary step records the cancellation argument.

The landing return reports an overlapping rollback after base `697485a8c`.
Re-read the current file and reconstructed the packet as its verbatim prefix plus
the proved general-site interface, retaining the current public helpers. The node
still attaches the general declaration although the rollback removed its source;
restoring the proved interface reconciles them. Removed the retained redundant
file-level `autoImplicit` setting; compilation already enforces that option.
No existing statement or definition correction was necessary. The additive API
change is recorded in `coord/changes/P3-restore-module-abelian-evaluation-general.md`.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
