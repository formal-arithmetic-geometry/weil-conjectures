## What changed

Replaced the sole sorry in `supported_integral_model_restriction_tower` by a complete
Lean assembly, preserving its signature and existing docstring. Constructed scalar
coordinates from the actual scalar natural endomorphisms, proved their exactness,
installed all resolution instances, constructed the strict etale descent by the
comparison counit, and proved marked uniqueness by full faithfulness. Constructed
the pulled-back tower identification and proved its precise normalization. Natural
endpoint isomorphisms and their commuting square are assembled with `Arrow.isoMk`.

Added three strictly separate intermediate statements, each with a new module and
node: finite quotient/pullback transport, normalized endpoint reconstruction, and
compatibility of already-normalized endpoints with restriction. The main theorem
contains no sorry. No definition or existing public statement was changed, and no
source-library file was edited. The original torsion-rigidity hypothesis is retained;
the proof clears it because the original plan reserves it for the consumer.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SupportedIntegral.supported_integral_model_restriction_tower`
(node `lem-sfb-supported-integral-model-restriction-tower`). This is a decomposition,
not an independent proof of the mathematics: 1 original hole closed, 3 holes added,
net -2 before other closure effects. The item itself now has zero sorry.

Every added sorry is exactly a named public theorem body:

- `AlgebraicGeometry.ProEtale.SupportedIntegral.supported_integral_finite_quotients`,
  node `lem-sfb-supported-integral-finite-quotients`.
- `AlgebraicGeometry.ProEtale.SupportedIntegral.supported_integral_endpoint_reconstruction`,
  node `lem-sfb-supported-integral-endpoint-reconstruction`.
- `AlgebraicGeometry.ProEtale.SupportedIntegral.supported_integral_restriction_square`,
  node `lem-sfb-supported-integral-restriction-square`.

The finite-quotient result asserts neither descent nor reconstruction. The endpoint
result assumes the marked descent and asserts no horizontal square. The square
result assumes the normalized endpoint isomorphisms and proves only their
compatibility. Thus none is the original statement with renamed or repackaged
hypotheses. The endpoint equations determine their maps after the invertible
finite comparison and marking; no arbitrary unmarked object is chosen in a definition.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `Sheaf.Paper.IntegralQuotientResolutionNormalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.Paper.FiniteModelSheafQuotientConstructible`.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`.
- `Sheaf.Paper.FiniteDiscreteScalarConstantModels`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical`.
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `Sheaf.Paper.PrincipalReductionConeCalculus`.
- `Sheaf.Paper.FiniteScalarLocalModelComplete`.
- `Sheaf.Paper.FiniteScalarOrdinaryQuotientComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`.
- `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`.
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.
- `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections`.
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.

These results remain dependencies of the explicitly separated quotient, endpoint
and square arguments, so no node or module is claimed globally unnecessary. In
particular the canonical comparison pullback construction remains used through the
public interface. The independent-coefficient tower module remains imported with
`import all` to reuse its proved generic `tower_grothendieck` helper; its homotopy
limit theorem remains part of the endpoint route. Pruned mathematical modules: none.

## Where the brief, the DAG or earlier work was wrong

The stated plan suppresses interface transport: the existing integral arithmetic,
quotient constructibility and local-model completion theorems are specialized to
canonical valuation-ring coefficients and a chosen uniformizer. This item allows
a topological ring isomorphism and any generator of the maximal ideal. Applying
those declarations directly does not type-check; the finite quotient node records
the required transport, including preservation of the actual quotient projections.

The internal/section-module equivalence is over the full section ring, whereas
`Coordinates` uses the constant scalar ring. The proof therefore constructs the
required fixed-scalar action explicitly from `scalar`, rather than confusing these
two coefficient categories. The original unit route and target statements are kept.

Edge cases were checked against the constructions: zero modules and empty schemes
have zero quotients; torsion models use the ordinary quotient tower and the strict
cone-to-quotient total-limit comparison, not a false levelwise derived identification;
the identity support path is covered by the same counit and whiskering formulas.
No assumption on the complement of the original closed immersion is added.

## New nodes

`lem-sfb-supported-integral-finite-quotients` states the finite-level properties and
normalized scalar pullback required before descent. Its new Lean module is
`Sheaf.Paper.SupportedIntegralFiniteQuotients`.

`lem-sfb-supported-integral-endpoint-reconstruction` states only the normalized
source and target reconstructions. Its module also names the exact endpoint
normalization predicates, copied from the existing comparison fields without
changing their equations. Its new module is
`Sheaf.Paper.SupportedIntegralEndpointReconstruction`.

`lem-sfb-supported-integral-restriction-square` asserts the commuting square for
already-constructed endpoint isomorphisms satisfying those equations. Its new
module is `Sheaf.Paper.SupportedIntegralRestrictionSquare`.

All three inherit the original chapter and unit, cite the original blueprint
argument, record Mathlib and blueprint searches, and carry complete proof plans.
No change record is needed: existing definitions and statements were unchanged.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
