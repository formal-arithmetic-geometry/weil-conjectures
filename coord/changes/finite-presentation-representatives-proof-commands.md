# AlgebraicGeometry.RingedSpace.exists_finitePresentation_representatives

## Reason

The stage-3 static gate classifies added top-level commands as potentially visible interface
changes. This packet adds `set_option autoImplicit false`, opens `CategoryTheory.Limits`
and `Opposite`, and adds a private irreducible overlap-isomorphism definition with a proved
section-map formula. These commands support elaboration of the proof. No existing public
signature, public definition, universe parameter, attribute or public import changes.
The removed import of `Sheaf.CategoryTheory.RingedSiteModules` was private; the gluing-data
import already supplies it. All new imports are private proof imports. This record documents
the static gate's concern; no downstream adaptation is necessary.

## Old

```lean
universe u

open CategoryTheory TopologicalSpace
```

```lean
theorem exists_finitePresentation_representatives
    (X : RingedSpace.{u}) :
    ∃ (I : Type u) (G : I → SheafOfModules.{u} (moduleRings X)),
      (∀ i : I, (G i).IsFinitePresentation) ∧
      ∀ F : SheafOfModules.{u} (moduleRings X), F.IsFinitePresentation →
        ∃ i : I, Nonempty (F ≅ G i)
```

## New

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
```

The theorem signature above stays verbatim. All added definitions and helper theorems are
private; the irreducibility attribute is attached only to the new private `modelTransition`.
The new definitions construct actual cokernels and composite isomorphisms and contain no holes.
The theorem proof uses existing stated gluing dependencies. Its docstring and DAG proof now
record the shorter finite-presentation route.

## Users

Source-only `tools/downstream.py Sheaf.Algebra.Category.ModuleCat.Sheaf.FinitePresentationRepresentatives --uses AlgebraicGeometry.RingedSpace.exists_finitePresentation_representatives`
reports the following downstream modules and the item itself. The only external direct user
of the theorem is `Sheaf.AlgebraicGeometry.FinitePresentationPairsFiltered`; its use retains
exactly the same statement and representatives. All public imports remain verbatim, so the
interfaces used by indirect consumers are preserved as well. No target definition changes,
and no statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AlgebraDirectedColimitFiniteType` | T6 | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.FinitePresentationPairsFiltered` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite` | P8 | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ModuleFilteredColimitFinitePresentation` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.IntegralFibreSectionSpecialization` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.IntegralHenselianLisseSectionRigidity` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.IntegralLisseClosedBaseChange` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveNaturality` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.NearbyCycleSheafFiniteness` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.PlurinodalProperHypercover` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.PsiGoodOrientedCohomologyStrata` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.RootBoundaryScalarComparison` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.RootTowerBoundaryAcyclicity` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.RootTowerInnerSupport` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.TameStratumKummerDescent` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Paper.TraitNearbyBaseChange` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.BoundedConstructibleTransport` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ExceptionalComponentSpecialization` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.FiniteEtaModificationGluing` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.FiniteFibreValuationDomination` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ReducedFibreModification` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.SemistableModificationFibreContractions` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.SemistableNormalTargetFactorization` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.SingleValuationSemistableExtraction` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.TemkinStableModification` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationCurveProjectivePreparation` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationExceptionalLocalCriterion` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationMarkingSemistableSeparation` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationModificationProperCompletion` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationNormalizedGraphModel` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationSemistableDominatesStable` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationStrictSemistableCofinality` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization` | unclaimed | No change to signatures, definitions or public imports; no adaptation. |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FinitePresentationRepresentatives` | U1 | No change to signatures, definitions or public imports; no adaptation. |

## Status

landed 20261023T131934-L-2174044 2026-10-23 (merge of deliver/U1/Sheaf.Algebra.Category.ModuleCat.Sheaf.FinitePresentationRepresentatives)
