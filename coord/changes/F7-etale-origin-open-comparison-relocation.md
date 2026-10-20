# etaleOriginOpenComparison and canonical open/direct-image comparisons

## Reason

The proper/open proof needs a general restriction-transport lemma. That lemma must refer to
these four comparisons, while the parent theorem must use the lemma. Move the existing
constructions into the lemma's new module and publicly reexport them from the original module
to avoid a circular import. This relocation is unrelated to file time limits.

## Old

The following definitions lived in Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange:

```lean
def etaleOriginOpenComparison (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T ⥤ proEtaleDerivedCategory T A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

def etaleOriginOpenCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
            (sfIntrinsicModuleEquivalence Y A).functor)) ≪≫
    mapDerivedCategoryCompIso _ _

def etaleOriginOpenExtensionComparison {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        etaleOriginOpenComparison A Y ≅
      etaleOriginOpenComparison A X ⋙ sfIntrinsicDerivedOpen A j :=
  isoWhiskerRight
      ((mapDerivedCategoryCompIso _ _).symm ≪≫
        mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j) ≪≫
        mapDerivedCategoryCompIso _ _) (sfIntrinsicDerivedEquivalence Y A).functor ≪≫
    isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
      (etaleOriginOpenCoordinates A j).symm

def etaleOriginOpenDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A Y).obj
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj K.obj) ≅
      (proEtaleConstantDerivedDirectImage f A).obj
        ((etaleOriginOpenComparison A X).obj K.obj) :=
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let rp := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus (ULift.{u + 1, u} A) f
  (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    ((N Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app K).symm ≪≫
      ((N Y).mapDerivedCategoryPlusCompatibility.app (re.rightDerivedFunctorPlus.obj K)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (ProEtale.fixedComparisonDirectImageMatePlus
          (ULift.{u + 1, u} A) f)).app K) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((N X).mapDerivedCategoryPlus.obj K)) ≪≫
      rp.rightDerivedFunctor.mapIso ((N X).mapDerivedCategoryPlusCompatibility.app K)) ≪≫
    (sfIntrinsicDerivedDirectImageComparison f A).symm.app ((N X).mapDerivedCategory.obj K.obj)
```

## New

The same definitions, with exactly the same signatures, universes and bodies, now live in
Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport. The original module has:

```lean
public import Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport
```

```lean
def etaleOriginOpenComparison (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T ⥤ proEtaleDerivedCategory T A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

def etaleOriginOpenCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
            (sfIntrinsicModuleEquivalence Y A).functor)) ≪≫
    mapDerivedCategoryCompIso _ _

def etaleOriginOpenExtensionComparison {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        etaleOriginOpenComparison A Y ≅
      etaleOriginOpenComparison A X ⋙ sfIntrinsicDerivedOpen A j :=
  isoWhiskerRight
      ((mapDerivedCategoryCompIso _ _).symm ≪≫
        mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j) ≪≫
        mapDerivedCategoryCompIso _ _) (sfIntrinsicDerivedEquivalence Y A).functor ≪≫
    isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
      (etaleOriginOpenCoordinates A j).symm

def etaleOriginOpenDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A Y).obj
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj K.obj) ≅
      (proEtaleConstantDerivedDirectImage f A).obj
        ((etaleOriginOpenComparison A X).obj K.obj) :=
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let rp := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus (ULift.{u + 1, u} A) f
  (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    ((N Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app K).symm ≪≫
      ((N Y).mapDerivedCategoryPlusCompatibility.app (re.rightDerivedFunctorPlus.obj K)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (ProEtale.fixedComparisonDirectImageMatePlus
          (ULift.{u + 1, u} A) f)).app K) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((N X).mapDerivedCategoryPlus.obj K)) ≪≫
      rp.rightDerivedFunctor.mapIso ((N X).mapDerivedCategoryPlusCompatibility.app K)) ≪≫
    (sfIntrinsicDerivedDirectImageComparison f A).symm.app ((N X).mapDerivedCategory.obj K.obj)
```

The five-arrow composite, witness conjugation and lambda retain their original signatures
and bodies. The etale interchange retains its signature and uses a definitionally equal
existing wrapper for the same specified choice:

Old body:
```lean
  (Etale.unboundedProperOpenInterchange (ULift.{u + 1, u} A)).choose_spec.choose
    (pullback.fst p i) (pullback.snd p i) p i (IsPullback.of_hasPullback p i).toCommSq
```
New body:
```lean
  Etale.properOpenCoefficientInterchange (ULift.{u + 1, u} A)
    (IsPullback.of_hasPullback p i)
```
The wrapper unfolds to exactly the old body. Its named interface avoids repeatedly
elaborating the choice expression; no independently selected isomorphism is introduced. The new public import also makes the
general restriction theorem and its two explicit composite definitions visible. No old
constant acquires a new hypothesis or changes its mathematical meaning. The target statements
and the meanings of the definitions they use stay identical; the independent reader should
verify this relocation and reexport.

## Users

The table includes the earlier 219-module downstream scan and the final scan (whose current
import graph lists two downstream modules). Direct textual consumers include
Sheaf.Paper.CompactSupportUniformTorBound and, in the earlier scan,
Sheaf.SecSmoothPurity.IntrinsicCoefficientSiteMate,
Sheaf.SecSmoothPurity.ProperIntrinsicFiniteCoefficientExtension, and
Sheaf.SecSmoothPurity.ReductionDirectImage. Their terms keep the same constants by public
reexport. No source adaptation is necessary or delivered. Holders are read at packet creation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | F7 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | J3 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | B2 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCoefficientSiteMate | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ProperIntrinsicFiniteCoefficientExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | D9 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | M9 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | G8 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| TargetsCheck | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |

| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Unchanged names, signatures, bodies and public reexport; no adaptation. |

## Status

landed 20261020T051254-L-1616471 2026-10-20 (merge of deliver/F7/Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange)
