## What changed

Proved five existing theorems in `Sheaf.Paper.RationalRealizationScalarCoherence` from
its stated dependencies. No existing signature, structure field or definition changed.
The private coefficient-extensionality and comparison-uniqueness proofs identify an
arbitrary normalized comparison with the explicit balanced-localization comparison.
Its integral normalization is verified by cancelling the actual object transports and
balancing inverse. This permits the declared tower, identity and normalized-stage laws
to apply to the caller's comparison, including repeated fields. Identity geometric
pullback is assembled from the existing normalized pullback identity theorem, retaining
its specified site projection, ordinary map, computation equation and raw alpha law.

Added private proof imports of `RationalScalarBalancedLocalization` and
`RationalPullbackCompositionCoherence`. Both import-direction checks pass.
The DAG now records the normalization cancellation and direct identity dependency;
its existing completion and mixed arguments remain for the six unchanged holes.

## Proved and sorry left

Closed five of the original eleven holes (all names below are in
`AlgebraicGeometry.Scheme`):

- `rationalRealizationScalarCoherence`
- `rationalRealizationScalarTower`
- `rationalRealizationScalarUnit`
- `rationalScalarPullIdentity`
- `rationalRealizationStageTower`

Added zero holes and split off zero theorems. Six original named public holes remain,
all attached to `lem-per-rational-realization-scalar-coherence` and retaining their
existing source and proof docstrings:

- `rationalRealizationScalarMixed`
- `rationalRealizationScalarPentagon`
- `rationalRealizationScalarMixedTower`
- `rationalScalarPullComposition`
- `rationalRealizationScalarMixedComp`
- `rationalRealizationScalarMixedIdentity`

These proofs use the existing named dependency statements, some of which remain
unproved; this delivery closes the parent holes from those statements.

## No longer needed

Removed the following redundant direct private imports. Their needed interfaces are
already supplied by the retained public imports or the two actual proof dependencies:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.IntegralUniformCoefficient`
- `Sheaf.Paper.ContinuousConstructibleModule`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.RationalModuleRealizationFunctor`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.ContinuousCoefficientRealizations`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.CategoryTheory.FiniteFreeCompletionTransport`
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`
- `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.Paper.RingedPushforwardCompletion`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

No node, module, public import or upstream declaration is withdrawn. In particular,
the completed-unit-square and mixed-unit-cancellation nodes remain needed for the
six unchanged parent holes. Import removal here removes redundant direct edges;
it does not claim those mathematical dependencies are globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The module has eleven original holes. Its proof dependencies already state the canonical scalar comparison and coherence equations, so no new split-off
statement is needed for the five closed holes. Their maps must be related to the
arbitrary supplied comparison records by the normalization uniqueness argument;
endpoint isomorphism existence alone would not suffice.

The existing pullback identity dependency also includes an explicit identity
comparison on cochain complexes. Its component is the identity morphism, which is
removed before matching the parent's displayed computation equation. No mathematical
statement correction or forced consumer adaptation is made.

Source check: Bhatt--Scholze pp. 58--62, Lemma 6.8.2, Proposition 6.8.14(2),
and Remark 6.8.15 were read from the local PDF. They identify completed coefficients
with continuous functions, invert the coefficient parameter, and describe geometric
pullback as inverse image followed by coefficient tensor. The delivery uses the
existing declared balancing and normalization interfaces for these operations.
The unit record `sk-p-dl-a1-perverse` and its current blueprint section were read;
none of its realized statement or proof-step nodes is bypassed or withdrawn.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
