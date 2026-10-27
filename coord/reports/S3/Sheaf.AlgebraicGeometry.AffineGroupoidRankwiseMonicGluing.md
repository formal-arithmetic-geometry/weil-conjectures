## What changed

Proved `AlgebraicGeometry.affineGroupoid_rankwise_monic_gluing` in its assigned module,
with its statement and all public imports preserved. Server single-file compilation passed
in 16.7 seconds; the final delivery reruns compilation and the axiom probe. Private proved helpers convert the two
existing groupoid predicates and identify sections on a disjoint open cover with their product.
The main proof constructs the equalizer-ring equivalence, the exact prescribed padded polynomial,
and its component and evaluation formulas. Updated the assigned DAG proof to this argument.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.affineGroupoid_rankwise_monic_gluing`
(node `lem-a1-affine-groupoid-rankwise-monic-gluing`). No holes added or split off; no `sorry`
remains in this delivery. The existing imported rank-strata theorem remains a dependency.

## No longer needed

Removed the unused proof imports `Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections`
and `Mathlib.Topology.Sheaves.CommRingCat`; the proof imports
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing` and
`Mathlib.Algebra.Polynomial.Eval.Coeff` instead.

The binary-product induction and dependency `lem-weil-pbc-sheaf-disjoint-union-product`
are unnecessary: Mathlib unique sheaf gluing handles the whole indexed cover directly,
including an empty cover. No Sheaf module is withdrawn. All geometric rank-strata dependencies
remain behind the imported rank-strata theorem.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The empty case does not require a separate construction
of product isomorphisms: unique sheaf gluing includes it. Monicity of the constructed polynomial
also follows without imposing a separate nontriviality assumption on the invariant ring.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
