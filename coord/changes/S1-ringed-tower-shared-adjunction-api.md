# CategoryTheory.flatKFlat and the resolving-adjunction helper API

## Reason

Repair of returned delivery e9f56cc03e: the tower acyclicity file copied four private
helpers from `RingedToposDerivedPushforwardComposition`. Keep a single implementation:
export the existing `isIso_map_of_adjoints`, `flatKFlat`, and `flatKFlat_resolutions`
in the unclaimed composition module, and import that API in tower acyclicity.
`hom_localization_bijective` and `postcomp_bijective` remain private in their original
module, used by `isIso_map_of_adjoints`; their tower copies are deleted.

The former conjunction-valued `flatKFlat` is made a proposition-valued structure with
exactly the same K-flatness and flat-term fields. This preserves the predicate's meaning
and avoids repeatedly expanding its tensor realizations during elaboration. Its two
internal consumers use named field projections and construct the structure explicitly.
The two definition modules needed by its now-public signature become public imports.
No existing public theorem signature changes, and no target meaning changes.

## Old

```lean
private theorem isIso_map_of_adjoints
    {A B E DA DB DE : Type*}
    [Category* A] [Category* B] [Category* E]
    [Category* DA] [Category* DB] [Category* DE]
    {FL : B ⥤ A} {FR : A ⥤ B} (af : FL ⊣ FR)
    {GL : E ⥤ B} {GR : B ⥤ E} (ag : GL ⊣ GR)
    (WB : MorphismProperty B) [WB.HasRightCalculusOfFractions]
    (WE : MorphismProperty E) [WE.HasRightCalculusOfFractions]
    (QA : A ⥤ DA) (QB : B ⥤ DB) [QB.IsLocalization WB]
    (QE : E ⥤ DE) [QE.IsLocalization WE]
    (PB : ObjectProperty B) (PE : ObjectProperty E)
    (hresB : ∀ X : B, ∃ (X' : B) (s : X' ⟶ X), PB X' ∧ IsIso (QB.map s))
    (hresE : ∀ X : E, ∃ (X' : E) (s : X' ⟶ X), PE X' ∧ IsIso (QE.map s))
    (hinvf : ∀ {X Y : B}, PB X → PB Y → ∀ s : X ⟶ Y,
      IsIso (QB.map s) → IsIso (QA.map (FL.map s)))
    (hinvg : ∀ {X Y : E}, PE X → PE Y → ∀ s : X ⟶ Y,
      IsIso (QE.map s) → IsIso (QB.map (GL.map s)))
    (hgood : ∀ X : E, PE X → PB (GL.obj X))
    (I : A) (hI : ∀ X : A, Function.Bijective (QA.map : (X ⟶ I) → _))
    (T : B) (hT : ∀ X : B, Function.Bijective (QB.map : (X ⟶ T) → _))
    (j : FR.obj I ⟶ T) [IsIso (QB.map j)] : IsIso (QE.map (GR.map j))
```

```lean
private def flatKFlat
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) : ObjectProperty (HomotopyCategory
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (ComplexShape.up ℤ)) :=
  fun X ↦ CochainComplex.IsAcyclicTensorKFlat X.as ∧
    ∀ n : ℤ, SheafOfModules.IsFlat (X.as.X n)

private theorem flatKFlat_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] :
    ∀ X, ∃ (P : _) (s : P ⟶ X), flatKFlat J R P ∧ IsIso (DerivedCategory.Qh.{w}.map s)
```

## New

```lean
theorem isIso_map_of_adjoints
    {A B E DA DB DE : Type*}
    [Category* A] [Category* B] [Category* E]
    [Category* DA] [Category* DB] [Category* DE]
    {FL : B ⥤ A} {FR : A ⥤ B} (af : FL ⊣ FR)
    {GL : E ⥤ B} {GR : B ⥤ E} (ag : GL ⊣ GR)
    (WB : MorphismProperty B) [WB.HasRightCalculusOfFractions]
    (WE : MorphismProperty E) [WE.HasRightCalculusOfFractions]
    (QA : A ⥤ DA) (QB : B ⥤ DB) [QB.IsLocalization WB]
    (QE : E ⥤ DE) [QE.IsLocalization WE]
    (PB : ObjectProperty B) (PE : ObjectProperty E)
    (hresB : ∀ X : B, ∃ (X' : B) (s : X' ⟶ X), PB X' ∧ IsIso (QB.map s))
    (hresE : ∀ X : E, ∃ (X' : E) (s : X' ⟶ X), PE X' ∧ IsIso (QE.map s))
    (hinvf : ∀ {X Y : B}, PB X → PB Y → ∀ s : X ⟶ Y,
      IsIso (QB.map s) → IsIso (QA.map (FL.map s)))
    (hinvg : ∀ {X Y : E}, PE X → PE Y → ∀ s : X ⟶ Y,
      IsIso (QE.map s) → IsIso (QB.map (GL.map s)))
    (hgood : ∀ X : E, PE X → PB (GL.obj X))
    (I : A) (hI : ∀ X : A, Function.Bijective (QA.map : (X ⟶ I) → _))
    (T : B) (hT : ∀ X : B, Function.Bijective (QB.map : (X ⟶ T) → _))
    (j : FR.obj I ⟶ T) [IsIso (QB.map j)] : IsIso (QE.map (GR.map j))
```

```lean
/-- A K-flat homotopy complex whose terms are flat module sheaves.

The structure keeps the two properties available without unfolding tensor realizations. -/
structure flatKFlat
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (X : HomotopyCategory
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (ComplexShape.up ℤ)) : Prop where
  kflat : CochainComplex.IsAcyclicTensorKFlat X.as
  flat (n : ℤ) : SheafOfModules.IsFlat (X.as.X n)

/-- Every module homotopy complex admits a flat-term K-flat resolution. -/
theorem flatKFlat_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] :
    ∀ X, ∃ (P : _) (s : P ⟶ X), flatKFlat J R P ∧ IsIso (DerivedCategory.Qh.{w}.map s)
```

Only visibility changes in the generic theorem; its proof is unchanged. In the
composition proof, the good-object map constructs `flatKFlat` from the two properties
returned by the K-flat pullback API. `flatKFlat_inverts` reads `.kflat` and `.flat`.
These internal adaptations keep every original public statement and visibility.

## Users

The source scan `tools/downstream.py` with `--uses CategoryTheory.isIso_map_of_adjoints
CategoryTheory.flatKFlat CategoryTheory.flatKFlat_resolutions` found 702
transitive importers. None mentions any changed helper: the only pre-existing uses
are in the composition module itself. These helpers were private, so importers could
not depend on them. The complete transitive importer list follows; no imported theorem
statement or definition depends on the changed predicate. The tower acyclicity file is
the one new direct consumer. No module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition | unclaimed | Export existing helpers; equivalent structured predicate; adapt its two internal uses. |
| Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic | S1 delivery | Delete duplicated helpers and import the shared API. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisonGeneral | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationAcyclic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImageCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SmoothLisseCompactDualExchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SmoothLisseRelativeDualBounded | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison | claimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteConstantCokernel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorRouteDescent | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ProEtaleConstantModuleConstructibility | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| TargetsCheck | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Composition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BidualitySupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDual | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBiduality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointBiduality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | claimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.Statement | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No reference to changed helpers; existing public theorem unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No reference to changed helpers; existing public theorem unchanged. |

## Status

landed 20261018T093506-L-3541548 2026-10-18 (merge of deliver/S1/Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison)

## Repair update

The returned duplicate-helper check also found that the assigned comparison copied the generic
`derives` and `exists_derived` statements already present in this module. Those two declarations
are now public, and the public imports required by their signatures were added. The comparison
module directly imports this module and uses these declarations; its two duplicate local helpers
were deleted. The generic theorem bodies and all existing public theorem statements are
unchanged.
