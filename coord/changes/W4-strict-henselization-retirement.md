# Retirement of AlgebraicGeometry.Scheme small strict henselization constructions

## Reason

The human-approved retirement item in coord/retire-items.tsv requires removing
Sheaf.AlgebraicGeometry.StrictHenselization. Its upstream base module already
provides strictHenselizationAffineDiagram with the exact body of the copy's
smallStrictHenselizationDiagram. The upstream StrictHenselizationExtension provides
smallStrictHenselizationColimitIso, smallStrictHenselizationCocone and
isColimitSmallStrictHenselizationCocone with the same types and constructions.
Loading the copy together with that extension fails with duplicate declaration
names, as recorded for StrictLocalMateContinuityPresentation and
StrictLocalDerivedExchangeLeray in coord/rework.tsv.

The correction replaces all 31 existing direct imports by imports of the upstream
extension, replaces the old diagram name in its nine existing consumer modules,
and withdraws the item module. There are 36 edited consumers in total; all are
unclaimed. In the structural-flatness proof, two unreachable fallback tactic
branches are removed after the diagram replacement, leaving the successful
colimit-cocone branches unchanged. No source-library file or target statement is changed. The item's Lean
attachment now names WeilConjectures.AlgebraicGeometry.StrictHenselization. The
Lean attachment of lem-sbc-pointed-etale-ring-colimit-base-map-naturality records
the updated diagram name in its otherwise identical signature.

Preflight additionally requires removing the unused private import
Sheaf.AlgebraicGeometry.LogSmoothDifferentialLocalFreeness in
LogSmoothDifferentialGenerators: that module is route-pivot dropped. Its imports
are otherwise already present, and its theorem is not used by any declaration
in this consumer. No declaration or proof body is changed there.

## Old

The withdrawn module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.CategoryTheory.Filtered.Final
public import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# Strict henselization from affine pointed neighbourhoods

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-prop-h2`, definition
`def-weil-pbc-strict-henselization-limit` (blueprint: def-weil-pbc-strict-henselization-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The ring diagram on the chosen small representative category.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def smallStrictHenselizationDiagram
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (SmallModel.{u} (strictHenselizationNeighbourhoods s))ᵒᵖ ⥤ CommRingCat.{u} :=
  (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.op ⋙
    strictHenselizationCoordinateRings s

/-- Canonical comparison from the small ring-written diagram to upstream's affine diagram. -/
noncomputable def smallStrictHenselizationColimitIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    colimit (smallStrictHenselizationDiagram s) ≅ strictHenselization s := by
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact Functor.Final.colimitIso F.op (strictHenselizationDiagram s)

/-- The small affine diagram's cocone with upstream's strict henselization as vertex. -/
noncomputable def smallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cocone (smallStrictHenselizationDiagram s) :=
  (colimit.cocone (strictHenselizationDiagram s)).whisker
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s).op

noncomputable def isColimitSmallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsColimit (smallStrictHenselizationCocone s) := by
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact (Functor.Final.isColimitWhiskerEquiv F.op _).symm
    (colimit.isColimit (strictHenselizationDiagram s))

end AlgebraicGeometry.Scheme
```

## New

The item is withdrawn via deleted.txt. Its landing representation is an empty
module:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The public source-library replacement interfaces are:

```lean
noncomputable def strictHenselizationAffineDiagram
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (SmallModel.{u} (strictHenselizationNeighbourhoods s))ᵒᵖ ⥤ CommRingCat.{u} :=
  (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.op ⋙
    strictHenselizationCoordinateRings s

noncomputable def smallStrictHenselizationColimitIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    colimit (strictHenselizationAffineDiagram s) ≅ strictHenselization s

noncomputable def smallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cocone (strictHenselizationAffineDiagram s)

noncomputable def isColimitSmallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsColimit (smallStrictHenselizationCocone s)
```

These are existing upstream declarations, not additions of this delivery.
The diagram bodies are literally identical; the cocones and comparison maps
agree by reflexivity after unfolding. In particular the geometric point,
coordinate rings, colimit object, cocone legs and universal property are preserved
for every universe and base scheme, with no extra hypothesis. Target meanings do
not change; no target semantic review is reopened.

## Users

The transitive-user list was checked with tools/downstream.py and a direct import
scan. The table includes each existing transitive user and each adapted module.
Unchanged bridge sources in the sandbox are solely for remote recompilation and
are byte-identical to the library; they do not enter the delivery diff.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleModuleStalkSpecialization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleSectionGermSpecialization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.EtaleStalkSpecialization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit | unclaimed | Import upstream StrictHenselizationExtension; Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | W7 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.GeometricDimensionFunction | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityStrictFibreComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.LogBlowupNormalization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.LogRegularCompletedChart | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.LogRegularMonomialTensor | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.LogSmoothDifferentialGenerators | unclaimed | Import upstream StrictHenselizationExtension; remove unused private route-pivot dropped LogSmoothDifferentialLocalFreeness import as required by preflight. Declarations unchanged. |
| Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.LogSmoothLogRegular | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitBaseMapNaturality | unclaimed | Import upstream StrictHenselizationExtension; Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat | unclaimed | Use definitionally equal strictHenselizationAffineDiagram; remove two unreachable fallback tactic branches. Statement and successful proof branches unchanged. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence | V1 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | A2 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProjectiveStrictLocalIntersectionAcyclic | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | Q5 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | W9 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeff | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffFractionTrdeg | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationLimit | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationRestriction | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality | unclaimed | Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseAffine | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseGeometry | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseGlobalGerms | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseIndEtale | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseSections | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalCoefficientChart | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalCoefficientPresentation | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalConstantComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalModuleSectionsSetTransport | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalRationalChart | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | H2 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.DeligneLaumon.TraitLogSmoothUniformizerChart | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.FieldTheory.StrictHenselianFractionInertia | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | S4 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.CompactSupportSiteCoherence | U2 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.DeltaRestriction | X9 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.OrientedAffineNeighbourhoodLimit | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.OrientedTripleLimitDescent | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.ProperOpenTowerComparison | Q4 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.QcqsOrientedTriplePresentation | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.RealBoundaryLocalConstants | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.StrictHenselizationFunctoriality | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.StrictHenselizationMapExists | unclaimed | Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.StrictHenselizationPointEvaluation | unclaimed | Import upstream StrictHenselizationExtension; Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.StrictHenselizationPointEvaluationComparison | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.StrictHenselizationPointEvaluationImage | unclaimed | Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.StrictHenselizationPointEvaluationPointed | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.StrictHenselizationPointEvaluationProperties | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.StrictHenselizationPointedMap | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.RingTheory.CompleteToricFacetValuations | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.RingTheory.CompleteToricModel | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.RingTheory.StrictHenselizationFiniteLifts | unclaimed | Import upstream StrictHenselizationExtension; Use definitionally equal strictHenselizationAffineDiagram. Existing statements and proofs otherwise unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | X3 | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.TraceFormula.CompleteToricKatoRecognition | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.CompleteToricMonomialFactors | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.DivisorialLogChart | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.FiniteBaseStrictLocalization | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.TraceFormula.KatoTorIndependenceChart | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.TraceFormula.LogRegularDesingularization | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.LogRegularDivisorialStructure | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.LogRegularToricRefinement | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.NormalGenericArrowTransitivity | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.PointArrowsStrictLocalLifts | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.SmoothGeometricStalkAlgebra | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |
| Sheaf.TraceFormula.StrictHenselizationQuasiFiniteRing | unclaimed | Import upstream StrictHenselizationExtension. Existing statements and proofs otherwise unchanged. |
| Sheaf.TraceFormula.StrictHenselizationTensorFinite | unclaimed | No source edit; upstream replacements have definitionally identical types and bodies. |

## Status

landed 20261020T145547-L-2412568 2026-10-20 (merge of deliver/W4/Sheaf.AlgebraicGeometry.StrictHenselization)
