## What changed

Proved `WeilConjectures.complete_residue_cohomology_bounds` from the existing APIs and the
separate flat-term coefficient-filtration result
`WeilConjectures.integralReductionFlatFiltration`. The theorem signature is verbatim unchanged.
The private proved helpers `tor_vanishes` and `limit_bounds` handle the tensor-unit test
and the homology sequence of a Roos triangle. The proof uses a flat-term replacement of
the K-flat resolution from completeness and the recorded comparisons to retain its actual
canonical transitions. It then proves all finite-level bounds and top-degree epimorphy
by induction and applies exact products and the epimorphic-tower theorem directly to the
Roos triangle supplied by completeness. Both sandbox modules compile via lcompile.py --all.

The instance-removal commands are declaration-scoped with `in`, and the two
private instance proofs are registered only locally. The proof-scope record is
`coord/changes/CompleteResidueCohomologyBounds-proof-scope.md`. The unchanged direct
consumer `ResidueLisseProjectiveModels` compiles against the delivered parent in
4.4 seconds. The unchanged `FieldStageOrdinaryRealization` times out both against
the delivered parent and against the published parent; no consumer is adapted.

The new module is `Sheaf.Paper.IntegralReductionFlatFiltration`. It states the short exact
sequence of actual termwise reduction complexes, with the specified quotient transition.
It requires only flat terms; no completeness, Tor amplitude, cohomology interval or
quasi-compactness is assumed. Its docstring gives the coefficient calculation,
B-linearity, sheafification, tensoring and chain-map identification.

## Proved and sorry left

Closed the original hole `WeilConjectures.complete_residue_cohomology_bounds`
(node `lem-sf-complete-residue-cohomology-bounds`); no sorry remains in the item module.
Added one hole: `WeilConjectures.integralReductionFlatFiltration`
(node `lem-sf-integral-reduction-flat-filtration`). Its proof is exactly `by sorry`.
This is a decomposition, closing one upper hole and adding one strictly smaller lower
hole, not a net hole reduction. The lower statement is the flat-complex coefficient
sequence alone; the completed proof combines it with residue vanishing, replacement
comparison, induction and a Roos-triangle homology argument. No definitions or axioms added.

Further proof work verified the ordinary domain quotient calculation, including
injectivity, the kernel identity and linearity over the higher quotient ring, in a
compiled scratch experiment. The remaining formal work is the coefficient-sheaf
comparison and its compatibility with the chosen change-of-rings functors and canonical
chain maps. These are part of the separate filtration result, not additional assumptions
of the parent theorem. After scoping the instance commands, a fresh sandbox
compile checked both delivery modules without warnings (the parent took 14.7 seconds).

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`;
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`;
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`;
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`;
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.

The direct Roos-triangle argument does not need `det-pe-milnor-sequence` or
`det-pe-products-derived`; their approved tool-use entries were removed from the parent
node. It does use the already proved `det-pe-products-exact` and the derived-product
preservation clause of `lem-weil-derived-limit-existence`. The uniqueness-of-derived-limits
clause is unnecessary. The flat-sheaf definition is used by the new filtration lemma,
not directly by the parent. The separate cochain-model and coefficient-sized Tor APIs
are unnecessary here: the existing reduction comparison and original Tor predicate fit.
The K-flat resolution theorem, complex-SES triangle, long homology sequence, and
Milnor epimorphic theorem remain needed. Public statement imports are retained.
No assertion is made that a removed module becomes globally unreachable through other parents.

## Where the brief, the DAG or earlier work was wrong

The defining witness of derived completeness is K-flat, without termwise flatness.
The earlier local htri hole could not be justified by assuming its terms flat. The
proof now replaces that resolution by a genuinely flat-term one, and transports the
triangle back by the actual canonical integralTowerComparison isomorphisms and their
transition identity. The natural-number index n denotes exponent n+1; the new lemma
uses 0, n+1, n, corresponding to exponents 1, n+2, n+1.

The original step 6 constructed a new Milnor cone and compared derived limits. That
is unnecessary because completeness already supplies the required Roos triangle.
The parent node now records the direct homology proof. The unit sk-rem-sf-pf-done has
empty realized statement and step lists; its route and chapter are unchanged.

The resumed sandbox initially had no report or delivery. The initial dry run reported
`report.md is missing`; no prior delivery was pushed. Earlier logs recorded transient
compile-service transport failures. Current successful compiles validate the retained
and repaired proof. No launcher script or shared repository source was edited.

## New nodes

`lem-sf-integral-reduction-flat-filtration`, in sec-six-functors / sk-rem-sf-pf-done,
records the flat-complex coefficient short exact sequence from Stacks Tag 0942.
Its theorem is strictly below the cohomological-bounds argument and includes the actual
canonical quotient transition. Checks: n=0 is 0 -> R/(pi) -> R/(pi^2) -> R/(pi) -> 0;
the zero complex and empty site give zero sequences. For arbitrary n, pi is nonzero in
the DVR, so the cancellation and kernel calculation are valid. No assertion is made
for an arbitrary nonflat complex. No existing statement or definition was changed,
and no consumer adaptation is required. The proof-scope change record is
`coord/changes/CompleteResidueCohomologyBounds-proof-scope.md`.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
