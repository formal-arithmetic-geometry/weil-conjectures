# AlgebraicGeometry.ProEtale.finiteSiteCounitProjectionTransport

## Reason

The ten completed proofs need local elaboration controls to prevent repeatedly unfolding the
large tensor, projection, compact-support comparison and derived-functor constructions.
Profiling showed expensive class searches for the actual finite coefficient ring. The
existing projection and finite compact projection modules use the same local opacity and
finite-ring noetherianity priority. These are proof-context changes only.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

The existing module had no local instance-priority or irreducibility attributes. Its
eleven theorem proofs were `by sorry`. Public imports and signatures are unchanged.

## New

```lean
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance 2000] isNoetherian_of_finite CommRing.toRing
attribute [local irreducible] Etale.derivedTensor derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso derivedOpenImmersionLowerShriekProjectionIso
  compactSupportSiteComparison
```

Before the tensor theorem, `CommRing.toRing` returns to its original instance priority
100, and tensor/projection/comparison definitions are locally restored to semireducible:
its statement requires definitional matching of their displayed tensor/pullback endpoints.
The projection proofs above retain their local opacity. Explicit local map types then
prevent inference from expanding the geometric constructions during the tensor proof.

These local attributes change no exported reducibility hint, instance priority, signature,
construction, or public import. No private helper declaration or metaprogram is retained.
The ten completed proofs use existing named declarations. The original tensor-pair theorem
remains unfinished with its original signature and sourced proof docstring.
No public statement or helper axiom is added. The private `import all` lines reuse proved
generic helpers at the actual lifted finite coefficient ring. No consumer adaptation is required.

## Users

`tools/downstream.py Sheaf.Paper.FiniteSiteCounitProjectionTransport --uses
finiteSiteCounitProjectionTransport` reports the following 16 downstream modules and
only the item's own occurrence of the selected declaration. Every public theorem
signature is byte-identical, including all hypotheses, universes and normalizations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | U8 (dispatched item) | Ten proof bodies filled; tensor-pair hole retained; local proof context only. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | D4 | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | C9 | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | Identical public signatures, definitions and imports; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed | Identical public signatures, definitions and imports; no adaptation. |

## Status

landed 20261025T203408-L-2812189 2026-10-25 (merge of deliver/U8/Sheaf.Paper.FiniteSiteCounitProjectionTransport)
