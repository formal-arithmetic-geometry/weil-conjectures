## What changed

Proved `AlgebraicGeometry.ProEtale.integral_reduction_pullback_normalization` with
its exact existing signature. A proved private generic helper identifies the
component of an inverse mate with its adjunction transpose. Specializing this
identity identifies `integralReductionPullbackMap` with the existing
`FreeParameterEvaluation.scalarPullComparison`; its existing invertibility theorem
gives the natural isomorphism. Mathlib `unit_mateEquiv_symm` supplies the exact
scalar-unit equation, with the prescribed `derivedComapUpperStarIso` inverse.

Replaced the two private proof imports by `Sheaf.Paper.FreeParameterScalarMaps`.
All public imports and definitions are unchanged. Updated the item's node proof,
proof dependencies and proof origin to describe the argument actually used.
The new dependency is an existing general tool, valid for arbitrary commutative
condensed coefficients and every scheme morphism; it does not change the unit route.
The unit record `sk-thm-sf-pf-adic` has empty realized lists. Both the Lean import
check and a traversal of the new dependency's DAG edges find no cycle back here.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.integral_reduction_pullback_normalization`
(node `lem-sfb-integral-reduction-pullback-normalization`).
The private helper `inverseMate_app` is proved. Zero holes remain in the item;
zero holes and zero split-off statements are added.
The proof uses the existing theorem
`AlgebraicGeometry.ProEtale.FreeParameterEvaluation.scalarPullComparison_isIso`,
which still has its own existing sorry, attached to
`def-sfb-free-parameter-scalar-maps`. This is a proof from an existing dependency,
not an unconditional closure of all transitive axioms.

## No longer needed

Removed private imports `Sheaf.Paper.InternalScalarPullbackNormalization` and
`Sheaf.Paper.ModuleRingedToposDerivedComparison`. The corresponding nodes
`lem-sfb-internal-scalar-pullback-normalization` and
`lem-pd-module-ringed-topos-derived-comparison` are no longer direct proof
dependencies of this item. The proof does not need section realization,
computation-counit transport, or a new scalar-unit normalization lemma.
These dependencies may remain reachable from other public imports and other
consumers; this delivery does not withdraw their modules or declarations.

## Where the brief, the DAG or earlier work was wrong

The old plan proposed upgrading a computation-counit normalization to the unit
normalization here by a further K-flat calculation. That calculation is already
encapsulated in the existing general `scalarPullComparison_isIso` statement.
Its actual map is defined by exactly the scalar-unit transpose needed here.
The generic inverse-mate unit identity therefore supplies the remaining equation
without another split. Positive exponent one, empty schemes, zero complexes and
unbounded inputs are included because the general comparison and mate formula
have no additional hypotheses. The quotient map is not assumed flat.

Searches: LeanFinder for derived scalar extension commuting with geometric
pullback returned ordinary scalar/Kahler differential facts; Loogle found
`CategoryTheory.unit_mateEquiv_symm`; msearch grep confirmed that identity.
Local searches found `FreeParameterScalarMaps.scalarPullComparison_isIso` and
the analogous private component calculation in
`ScalarSixDerivedPullbackNormalization`. We used only the smaller former module.

Validation: the first server single-file compile succeeded in 30.4 seconds.
Its sole style suggestion (`have` in place of `haveI` for a proposition) was
applied before the delivery checks.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
