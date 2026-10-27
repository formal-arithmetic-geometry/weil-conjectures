# AlgebraicGeometry.AlgebraicSpace.space_line_module_proj_map

## Reason

The proof assembles scheme-test morphisms through the concrete Yoneda, over-category
and tensor-family definitions. The two transparency options permit elaboration to
identify these concrete expressions. The delivery preflight classifies the added
commands as a visible-command change and requires this record. Lean options here
control elaboration in this file; they change no declaration type or definition.
The statement tokens and the public imports are unchanged. No target meaning changes.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

The following is the complete transitive consumer list from tools/downstream.py.
Its --uses space_line_module_proj_map search finds only the assigned declaration;
consumers import the unchanged interface. No existing public declaration was added,
removed or changed in the assigned module, and no consumer requires editing.
New public lemmas are in the new Sheaf modules with their corresponding new nodes.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.TraceFormula.SpaceLineModuleProjMap` | N4 | Two local elaboration options; proof replaced. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.CommonMarkedNodalModel` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.CompleteFlagBundle` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | T2 | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback` | G3 | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.NodalLogDualizingPullback` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` | X5 | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.QuasiprojectiveQCComposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.RelativelyVeryAmple` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SectionIdealProjExpansion` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SeparatingPairOpen` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts` | J2 | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.VectorProjectivePresentation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LineZeroGeometry` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PlurinodalProperHypercover` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TraitNearbyBaseChange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.VectorFrameIntegrationSiteDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.AmpleNeighbourhood` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.BoundedConstructibleTransport` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.GradedImmersionAmpleCriterion` | S2 | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap` | N2 | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.PointedGenusZeroProjectiveLine` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.TemkinStableModification` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.ValuationMarkingSemistableSeparation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.ValuationNodalPolarSection` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.ValuationSemistableDominatesStable` | unclaimed | Unchanged public interface; no adaptation required. |

## Status

landed 20261023T151908-L-421279 2026-10-23 (merge of deliver/N4/Sheaf.TraceFormula.SpaceLineModuleProjMap)
