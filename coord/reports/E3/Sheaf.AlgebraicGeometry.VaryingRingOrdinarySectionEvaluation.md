## What changed

The assigned ordinarySectionEvaluation now follows from the existing ordinary
pullback/open compositor normalization and a bare clopen-projector comparison.
A proved private categorical calculation transports the projector through an
outgoing open extension and both compositors, including naturality, the inverse
pullback compositor, and equality transports for the two lift identities.
The original public statement, public imports and all construction bodies stay
unchanged. Only private proof imports and private proved helpers are added to
the item module. No existing other module or target statement is changed.

A private ComparisonCell record retains each comparison together with its source
and target functors. Equality transport uses its generic cellCompatible
predicate, keeping the chosen adjoint functors behind their existing interfaces.
Both ordinary cell constructors assign their fields explicitly from the original
functors and comparison isomorphisms. The compositor helpers take abstract
comparison families and their normalization hypotheses; the final proof substitutes
the specified families. This avoids expensive unfolding of chosen functors and
internal smallness proofs without changing shared definitions.

VaryingRingOrdinaryClopenProjectorEvaluation states and proves preservation of
one clopen projector. It uses a general proved adjunction argument: after
applying restriction, projector preservation follows from open-unit preservation
and naturality. Equality of maps into extension by zero is detected by the
restriction/direct-image adjunction, using the invertible clopen comparison.
This uses neither a choice of complementary open nor derived-evaluation
faithfulness.

The existing ordinaryOpen_mate supplies unit preservation. A proved private
unit_comparison helper applies the mate-unit equation and cancels the inverse
open comparison. No new unit-normalization statement or hole is introduced.

Validation: the final lcompile.py --all run compiled both modules with no
errors or warnings: 35.6 seconds for VaryingRingOrdinaryClopenProjectorEvaluation
and 41.3 seconds for VaryingRingOrdinarySectionEvaluation, each below 60 seconds.
The public imports and assigned statement are unchanged. Node dependency unions,
Lean attachments, report sections, line lengths and absence of sorries/debug
commands were also checked.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.VaryingRing.ordinarySectionEvaluation.
Also proved the new public theorem
AlgebraicGeometry.ProEtale.VaryingRing.ordinaryClopenProjectorEvaluation and all
private helpers used to combine these results.

The delivered Lean modules contain zero sorries: one original hole is closed
and zero holes are added or split off. The existing ordinaryComparisonNormalization
and ordinaryOpen_mate are used as declared; their proofs are outside this delivery. This does not assert that the dependency closure is
already free of holes.

## No longer needed

No public import is removed and no existing module is withdrawn or pruned.
The original direct dependency on def-weil-sheaf-of-modules-category is not used
as an independent proof step: the projection comparison is instead deduced
categorically from the adjoint triple and the open-unit equation. The module
category definitions remain used through their original constructions. The
strict-tower calculus remains needed for its proved projector image identity.
The section calculation uses no cartesian beta or cartesian evaluation theorem.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The existing ordinaryOpen_mate is the
needed one-open-adjunction normalization. Its unit characterization supplies
the projector argument, avoiding a duplicate unit-normalization obligation.
The section equation is obtained from this projector comparison and the existing
compositor normalization. clopenSectionEvaluation concerns derived evaluation
to a single coefficient category, so it is not used for ordinary realization.

Edge checks: the unit equation has no quasi-compactness or closedness assumption,
as neither is needed for the open adjunction. At the empty open its module
category is zero and the identity is the zero-object unit. At an identity open
it is the usual adjunction normalization. The projector argument applies also
to the empty and full clopen image. No finiteness, torsion, nonzero-ring or
positive-index hypothesis is introduced; n=0 and zero coefficient rings are
included.

## New nodes

lem-sp-varying-ring-ordinary-clopen-projector-evaluation attaches the proved
comparison for a single clopen projector. Its proof uses the ordinary projector
image identity, the strict calculus's projector image identity, the existing
ordinaryOpen_mate, naturality and injectivity of an adjunction equivalence.
The node retains the parent's chapter and unit. No new hole is introduced.

Searches used launcher LeanSearch, LeanFinder, Loogle and Mathlib grep,
supplemented by local reads of both library roots. The existing mate statement
supplies the normalization needed by the categorical argument.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
