# WeilConjectures.OpenFactorCoherence fixed data extraction

## Reason

The three strict-normalization realization lemmas must use the fixed Open,
OrdinaryExchange, gamma, theta and beta types before the assembly theorem. Extract
these existing declarations verbatim to OpenFactorCoherenceData and publicly
re-export them from OpenFactorCoherence. This removes an import cycle; no type,
field, value, attribute or existing public import changes.

## Old

```lean
set_option genSizeOf false in
set_option genInjectivity false in
/-- Canonical completion/open commutation and all of clauses (1) and (2).
The strict tower comparison is fixed by the actual quotient augmentation.
Source: Stacks 099N, 09BN, 0E8I
(blueprint: lem-sf-pf-open-factor-coherence). -/
structure Open {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] where
  tower : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ≅
    IntegralOnSlice.tower.{u, u} l E U none ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j)
  tower_unit : ∀ (P : Cx l E U) (n : ℕ),
    ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
        (op n) ≫ (tower.hom.app P).app (op n) =
      (jCx l E j).map (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))
  tower_unique : ∀ v : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ⟶
      IntegralOnSlice.tower.{u, u} l E U none ⋙
        (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j),
    (∀ (P : Cx l E U) (n : ℕ),
      ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
          (op n) ≫ (v.app P).app (op n) =
        (jCx l E j).map
          (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))) →
      v = tower.hom
  commutes : J l E j ⋙ C l E X ≅ C l E U ⋙ J l E j
  unit_commutes : ∀ K : D l E U,
    (eta l E X).app ((J l E j).obj K) ≫ commutes.hom.app K =
      (J l E j).map ((eta l E U).app K)
  commutes_unique : ∀ v : J l E j ⋙ C l E X ⟶ C l E U ⋙ J l E j,
    (∀ K : D l E U, (eta l E X).app ((J l E j).obj K) ≫ v.app K =
      (J l E j).map ((eta l E U).app K)) → v = commutes.hom
  restriction_complete : ∀ K : D l E X, IsSfDerivedComplete l E X K →
    IsSfDerivedComplete l E U ((star l E j).obj K)
  extension_complete : ∀ K : D l E U, IsSfDerivedComplete l E U K →
    IsSfDerivedComplete l E X ((J l E j).obj K)
  pull : Pull l E j
  pull_unit : ∀ K : D l E X, IsSfDerivedComplete l E X K →
    IsIso ((pull.unit l E).app K)
  restrictionIso : J l E j ⋙ star l E j ≅ 𝟭 (D l E U)
  section_unit : ∀ K : D l E U,
    (openDerivedAdjunction (completed l E) j).unit.app K ≫ restrictionIso.hom.app K = 𝟙 K
  fullyFaithful : ∀ (K L : D l E U), IsSfDerivedComplete l E U K →
    IsSfDerivedComplete l E U L → Function.Bijective
      (fun f : K ⟶ L ↦ (J l E j).map f)
  constructible : ∀ K : D l E U, sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X ((J l E j).obj K)
  restriction_constructible : ∀ P : D l E X, sfIntegralConstructible l E X P →
    sfIntegralConstructible l E U ((star l E j).obj P)
  reduction_iso : ∀ (K : D l E U) (n : ℕ), sfIntegralConstructible l E U K →
    IsIso ((PurCompactSupport.openComparison
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) j).app K)
  interval : ∀ (K : D l E U) (n : ℕ) (a b : ℤ),
    sfIntegralConstructible l E U K →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension.{u, u} l E U n).obj K) ⊆
      Set.Icc a b →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension.{u, u} l E X n).obj
      ((J l E j).obj K)) ⊆ Set.Icc a b

/-- Completion of the actual ambient open tensor map, transported to the recorded
completed tensor. This is the supplied gamma of def-exchange-projection.
Source: Stacks 0GL1 and Bhatt--Scholze 3.4.10
(blueprint: lem-sf-pf-open-factor-coherence). -/
def gamma {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (o : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X)
    (K : D l E U) (P : D l E X) :
    (integralCompletedTensor.{u, u} l E X).obj ((J l E j).obj K, P) ⟶
      (J l E j).obj ((integralCompletedTensor.{u, u} l E U).obj (K, (star l E j).obj P)) :=
  tX.comparison.inv.app ((J l E j).obj K, P) ≫
    (C l E X).map ((openProjectionIso (completed l E) j
      tU.ordinary tX.ordinary K P).hom) ≫
    o.commutes.hom.app (tU.ordinary.tensor.obj (K, (star l E j).obj P)) ≫
    (J l E j).map (tU.comparison.hom.app (K, (star l E j).obj P))

/-- The ordinary pullback square, with the published composition normalization.
Source: Stacks 0D6D (blueprint: lem-sf-pf-open-factor-coherence). -/
def theta {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} (sq : OpenImmersionSquare a j' j h) :
    star l E h ⋙ star l E j' ≅ star l E j ⋙ star l E a :=
  (geometricPullComposition (completed l E) j' h (completedPull_comp l E j' h)).symm ≪≫
    eqToIso (congrArg (fun f : U' ⟶ X ↦ star l E f) sq.w.symm) ≪≫
    geometricPullComposition (completed l E) a j (completedPull_comp l E a j)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The ambient base-change map is fixed by the inverse open-unit transpose.
Source: Stacks 09BN (blueprint: lem-sf-pf-open-factor-coherence). -/
structure OrdinaryExchange {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare a j' j h) where
  comparison : J l E j ⋙ star l E h ≅ star l E a ⋙ J l E j'
  inverse : ∀ K : D l E U,
    (openDerivedAdjunction (completed l E) j').homEquiv _ _ (comparison.inv.app K) =
      (star l E a).map ((openDerivedAdjunction (completed l E) j).unit.app K) ≫
        (theta l E sq).inv.app ((J l E j).obj K)

/-- The strict-reduction completed exchange, expressed through the quotient completion
comparisons. Pull.model retains the strict finite maps; Open.unit_commutes fixes the
extension/limit comparison. Source: Stacks 099N and 09BN
(blueprint: lem-sf-pf-open-factor-coherence). -/
def beta {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    {sq : OpenImmersionSquare a j' j h} (b : OrdinaryExchange l E sq)
    (oh : Pull l E h) (oa : Pull l E a) (oj' : Open l E j') (K : D l E U) :
    (integralDerivedPullback.{u, u} l E h).obj ((J l E j).obj K) ⟶
      (J l E j').obj ((integralDerivedPullback.{u, u} l E a).obj K) :=
  oh.comparison.inv.app ((J l E j).obj K) ≫
    (C l E X').map (b.comparison.hom.app K) ≫
    oj'.commutes.hom.app ((star l E a).obj K) ≫
    (J l E j').map (oa.comparison.hom.app K)

```

## New

The declarations in `## Old` occur verbatim in
`Sheaf.SixFunctors.OpenFactorCoherenceData`, in the same namespace and universes.
The item publicly imports that module. All existing public imports remain.
`Assertion` and `openFactorCoherence` remain in the item, with identical signatures.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenFactorCoherence | Y8 | Extracts definitions verbatim and publicly re-exports them; theorem signature unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.CompactSupportProjectionFormula | S4 | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | P2 | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No edit; same names, types and definitions through the existing public import. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | No edit; same names, types and definitions through the existing public import. |
All 77 transitive importers returned by downstream.py retain the same public
interface; none needs adaptation. No target meaning changes or review is reopened.

## Status

landed 20261025T102004-L-3764455 2026-10-25 (merge of deliver/Y8/Sheaf.SixFunctors.OpenFactorCoherence)
