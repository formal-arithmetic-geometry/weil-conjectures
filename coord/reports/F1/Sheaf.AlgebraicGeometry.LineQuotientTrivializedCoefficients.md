## What changed

Filled `AlgebraicGeometry.Scheme.Modules.line_quotient_trivialized_coefficients` without
changing its statement. Added private, proved coefficient and tensor-unit helpers in
the item module; all additional imports are private proof imports. The coefficient
ring map is an explicit composition of `DirectSum.toSemiring` with the canonical
symmetric grading decomposition. No data is selected from an unproved existence
statement.

The proof reuses the proved `evaluate_one`, `evaluate_mul`, and normalized-unit
transport helpers from `GradedImmersionAmpleCriterion`, and the tensor-frame product
and generator helpers from `InvertibleSectionRing`. Right unitality supplies the
degree-one normalization. The unit-ideal proof lifts coefficient 1 through affine
sections of q and the affine pullback tensor comparison, then uses tensor induction.
Updated the item's DAG proof to record this argument.

Validation: the delivered module compiled through `lcompile.py` with exit code 0
in 21.5 seconds, with no warnings. Its theorem statement is unchanged; the node
changes are confined to `proof`, `proof_deps`, and `proof_origin`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.line_quotient_trivialized_coefficients`
(node `lem-trf-line-quotient-trivialized-coefficients`).

Holes closed: 1. Holes added: 0. Remaining holes in the delivered module: none.
All new helpers have complete proofs. No split-off modules or nodes.

## No longer needed

None of the two original declared proof dependencies is pruned: the symmetric
algebra grading supplies the direct-sum decomposition and the affine pullback
section comparison supplies the finite tensor expression. No original import is
removed, no module is withdrawn, and the blueprint unit route is unchanged.

The maximal-ideal/stalk detour in the old proof plan is unnecessary: affine
surjectivity of q and of the open-pullback coefficient map gives coefficient 1
globally, and tensor induction puts it in the mapped irrelevant ideal.

## Where the brief, the DAG or earlier work was wrong

The old proof plan describes a stalk/maximal-ideal argument, but a shorter global
affine argument proves the same conclusion. The library already provides proved
private evaluation and tensor-frame helpers; no new unproved comparison is needed.
No mathematical statement, definition, target, or unit route has changed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
