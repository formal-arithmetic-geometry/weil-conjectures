## What changed

Proved `quotientExpressionStrictKFlatTowers_towerData` from the existing
coefficient reduction-system calculus and constructor lemmas. The generator
systems and their quotient squares come from `reductionModel`. Structural
induction supplies system flatness and K-flatness. The proof supplies horizontal
identity and composition, the actual completed-tower arrows, and all the specified
derived comparison maps. Its localization equation is a specialization of the
natural-transformation lifting formula.

Added `Sheaf.Paper.StrictQuotientCompletedHorizontal` for the exact section-map
formula after completed restriction. A generic comparison with the underlying
additive presheaf avoids an expensive kernel conversion; separating this
self-contained formula also keeps the tower proof within the per-file limit.
Added `Sheaf.Paper.StrictQuotientLevelwiseFlatModels`, with a proved equivalence
between system and levelwise flat-term K-flatness. All added imports are proof
imports; existing public statements, definitions and public imports are preserved.
All three delivered modules compile cleanly with `lcompile.py` within the
60-second limit; profiling options and temporary debug modules have been removed.

## Proved and sorry left

Closed the module's one original hole:
`WeilConjectures.StrictQuotient.quotientExpressionStrictKFlatTowers_towerData`,
node `lem-pur-quotient-expression-strict-kflat-towers-tower-data`.

Also proved the new supporting theorem
`WeilConjectures.StrictQuotient.levelwiseFlatModels`, node
`lem-pur-strict-quotient-levelwise-flat-models`.
Also proved `WeilConjectures.StrictQuotient.completedHorizontal`, node
`lem-pur-strict-quotient-completed-horizontal`.
No holes are added, and no `sorry` remains in any delivered Lean file.
The existing constant-map, unit-transition and final conjunction proofs remain.
This uses the existing stated reduction calculus and the existing
`strictTensorAdjointConstructor` and `strictPullbackAdjointConstructor`; it does
not claim to close the holes in those separate modules.

## No longer needed

No module is withdrawn, and no original public import is removed. No new
semilinear-system construction, reduction model, transition-formula statement or
pullback-evaluation statement is needed: the existing calculus and constructor
APIs provide them. Both new nodes are fully proved supporting lemmas.

The tower-data node no longer directly invokes
`lem-pur-proetale-constant-coefficient-comparison`,
`prop-weil-pbc-proetale-constant-ring-map`,
`prop-weil-pbc-proetale-constant-exact`,
`lem-pur-derived-change-of-rings`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pur-system-ringed-sequence-site`,
`lem-coef-semilinear-derived-sections`, or
`lem-weil-pbc-exact-functor-derived-functor`.
The constant coefficient square belongs to the separately proved constant-map
component. Flat preservation uses the ambient tensor data and independent
change-of-rings theorem; constructor clauses give finite pullback computations;
canonical exact-localization factors give derived evaluations and restriction.
Some of these results remain transitive dependencies. The ringed pullback
module remains a direct proof dependency for its proved flatness and K-flatness
isomorphism-transfer helpers; using those helpers avoids repeating their
monoidal instance construction in this file. No global pruning of their modules is claimed.

The definition nodes `def-weil-proetale-inverse-image`,
`def-weil-completed-integral-coefficients`, `def-pur-sheaf-tensor-product`,
`def-pc-tensor-complex-sheaves`, `def-pc-sheaf-restrict-scalars`,
`def-pc-flat-sheaf-modules`, and `def-pc-kflat-complex` remain statement
dependencies rather than separate direct proof steps.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The tower-data node previously delegated its whole
proof to a later worker in one step; its proof record now describes the actual
construction and comparison arguments. The existing constructor statements
already contain the required tensor transitions, pullback transitions and finite
pullback models. The unit's recorded route is preserved.

## New nodes

`lem-pur-strict-quotient-levelwise-flat-models` states the equivalence between
flat-term K-flatness on the vertical sequence site and at every positive
coefficient level. Forward detection uses the existing componentwise exactness
and tensor lemmas. For the reverse flatness implication, evaluate the K-flat
single complex of a flat term and apply the proved single-complex flatness
criterion. The result applies to arbitrary system complexes; no flatness of
coefficient quotients is assumed. No existing definition or statement changes,
so no change record is needed.

`lem-pur-strict-quotient-completed-horizontal` packages the proved horizontal-map
clause of the unique restriction functor, followed by the Mathlib comparison of
module-presheaf maps with their underlying additive maps. Its conclusion is just
the ordinary section formula, and is strictly part of the completed-tower clause.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
