# AlgebraicGeometry.ProEtale.CondensedRing.openSupportHomMap and companion maps

## Reason

Move the six existing concrete definitions into a shared module so that the independent support projection obligation and the parent theorem can both import them without a cycle. Names, types, visibility and bodies are unchanged. No target statement or coefficient definition changes.

## Old

Declared in Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom:

```lean
/-- The open extension/restriction adjunction, using the canonical alpha transport.
Source: Stacks Tag 09BN (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportDerivedAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⊣
      (supportPullback Λ j).mapDerivedCategory :=
  ((openImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (supportPullbackIsoUpperStar Λ j).symm).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (supportPullback Λ j).rightDerivedFunctorIsoMapDerivedCategory

/-- Closed inverse/direct-image adjunction, both functors exact and applied termwise.
Source: Stacks Tag 09AA (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def closedPullbackDerivedAdjunction {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (supportPullback Λ i).mapDerivedCategory ⊣ (lowerStar Λ i).mapDerivedCategory :=
  (supportPullbackAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory

/-- Open projection map: the adjunct of unit tensor identity followed by inverse tensor
comparison. Source: proof step 3 (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportProjection {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    (T : DerivedCategory (supportModules Λ X)) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (((derivedTensor Λ U).obj L).obj ((supportPullback Λ j).mapDerivedCategory.obj T)) ⟶
      ((derivedTensor Λ X).obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T :=
  ((openSupportDerivedAdjunction Λ j).homEquiv
    (((derivedTensor Λ U).obj L).obj ((supportPullback Λ j).mapDerivedCategory.obj T))
    (((derivedTensor Λ X).obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T)).symm
    (((derivedTensor Λ U).map ((openSupportDerivedAdjunction Λ j).unit.app L)).app
        ((supportPullback Λ j).mapDerivedCategory.obj T) ≫
      (supportDerivedTensorComparison Λ j
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) T).inv)

/-- Closed projection map: closed unit followed by pullback tensor comparison and closed
counit. Source: proof step 3 (blueprint: lem-sfb-open-closed-internal-hom-formulas).
Its direction uses the unit of i^* adjoint to i_*, never a nonexistent counit i_*i^* -> id. -/
noncomputable def closedSupportProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (P : DerivedCategory (supportModules Λ Z))
    (T : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj ((supportPullback Λ i).mapDerivedCategory.obj T)) :=
  (closedPullbackDerivedAdjunction Λ i).unit.app
      (((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T) ≫
    (lowerStar Λ i).mapDerivedCategory.map
      ((supportDerivedTensorComparison Λ i
        ((lowerStar Λ i).mapDerivedCategory.obj P) T).hom ≫
        ((derivedTensor Λ Z).map ((closedPullbackDerivedAdjunction Λ i).counit.app P)).app
          ((supportPullback Λ i).mapDerivedCategory.obj T))

/-- Open internal-Hom comparison determined by projection and evaluation transposes.
Source: proof steps 9 and 11 (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportHomMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    (N : DerivedCategory (supportModules Λ X)) :
    ((derivedHom Λ X).obj
      (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N ⟶
    (lowerStar Λ j).rightDerivedFunctor.obj
      (((derivedHom Λ U).obj (op L)).obj
        ((supportPullback Λ j).mapDerivedCategory.obj N)) :=
  let H := ((derivedHom Λ X).obj
    (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N
  let rH := (supportPullback Λ j).mapDerivedCategory.obj H
  let rN := (supportPullback Λ j).mapDerivedCategory.obj N
  (closedSupportOpenDerivedAdjunction Λ j).homEquiv H
    (((derivedHom Λ U).obj (op L)).obj rN)
    ((derivedTensorHomAdjunction Λ L).homEquiv rH rN
      ((openSupportDerivedAdjunction Λ j).homEquiv (((derivedTensor Λ U).obj L).obj rH) N
        (openSupportProjection Λ j L H ≫
          (derivedTensorHomAdjunction Λ
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).counit.app N)))

/-- Closed internal-Hom comparison using an inverse of the canonical closed projection.
Source: proof steps 10 and 11 (blueprint: lem-sfb-open-closed-internal-hom-formulas).
The theorem supplies its inverse projection as an isomorphism with specified hom. -/
noncomputable def closedSupportHomMap {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) (N : DerivedCategory (supportModules Λ X))
    (χ : (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj
          ((supportPullback Λ i).mapDerivedCategory.obj
            (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N))) ⟶
      ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)) :
    (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedHom Λ Z).obj (op P)).obj ((closedSupport Λ i j).rightDerivedFunctor.obj N)) :=
  let H := ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N
  let rH := (supportPullback Λ i).mapDerivedCategory.obj H
  let iN := (closedSupport Λ i j).rightDerivedFunctor.obj N
  (closedPullbackDerivedAdjunction Λ i).homEquiv H
    (((derivedHom Λ Z).obj (op P)).obj iN)
    ((derivedTensorHomAdjunction Λ P).homEquiv rH iN
      ((closedSupportDerivedAdjunction Λ i j hij).homEquiv (((derivedTensor Λ Z).obj P).obj rH) N
        (χ ≫ (derivedTensorHomAdjunction Λ
          ((lowerStar Λ i).mapDerivedCategory.obj P)).counit.app N)))

```

## New

Declared verbatim in `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps`, publicly reexported by the original module:

```lean
/-- The open extension/restriction adjunction, using the canonical alpha transport.
Source: Stacks Tag 09BN (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportDerivedAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⊣
      (supportPullback Λ j).mapDerivedCategory :=
  ((openImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (supportPullbackIsoUpperStar Λ j).symm).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (supportPullback Λ j).rightDerivedFunctorIsoMapDerivedCategory

/-- Closed inverse/direct-image adjunction, both functors exact and applied termwise.
Source: Stacks Tag 09AA (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def closedPullbackDerivedAdjunction {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (supportPullback Λ i).mapDerivedCategory ⊣ (lowerStar Λ i).mapDerivedCategory :=
  (supportPullbackAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory

/-- Open projection map: the adjunct of unit tensor identity followed by inverse tensor
comparison. Source: proof step 3 (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportProjection {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    (T : DerivedCategory (supportModules Λ X)) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (((derivedTensor Λ U).obj L).obj ((supportPullback Λ j).mapDerivedCategory.obj T)) ⟶
      ((derivedTensor Λ X).obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T :=
  ((openSupportDerivedAdjunction Λ j).homEquiv
    (((derivedTensor Λ U).obj L).obj ((supportPullback Λ j).mapDerivedCategory.obj T))
    (((derivedTensor Λ X).obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T)).symm
    (((derivedTensor Λ U).map ((openSupportDerivedAdjunction Λ j).unit.app L)).app
        ((supportPullback Λ j).mapDerivedCategory.obj T) ≫
      (supportDerivedTensorComparison Λ j
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) T).inv)

/-- Closed projection map: closed unit followed by pullback tensor comparison and closed
counit. Source: proof step 3 (blueprint: lem-sfb-open-closed-internal-hom-formulas).
Its direction uses the unit of i^* adjoint to i_*, never a nonexistent counit i_*i^* -> id. -/
noncomputable def closedSupportProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (P : DerivedCategory (supportModules Λ Z))
    (T : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj ((supportPullback Λ i).mapDerivedCategory.obj T)) :=
  (closedPullbackDerivedAdjunction Λ i).unit.app
      (((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T) ≫
    (lowerStar Λ i).mapDerivedCategory.map
      ((supportDerivedTensorComparison Λ i
        ((lowerStar Λ i).mapDerivedCategory.obj P) T).hom ≫
        ((derivedTensor Λ Z).map ((closedPullbackDerivedAdjunction Λ i).counit.app P)).app
          ((supportPullback Λ i).mapDerivedCategory.obj T))

/-- Open internal-Hom comparison determined by projection and evaluation transposes.
Source: proof steps 9 and 11 (blueprint: lem-sfb-open-closed-internal-hom-formulas). -/
noncomputable def openSupportHomMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    (N : DerivedCategory (supportModules Λ X)) :
    ((derivedHom Λ X).obj
      (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N ⟶
    (lowerStar Λ j).rightDerivedFunctor.obj
      (((derivedHom Λ U).obj (op L)).obj
        ((supportPullback Λ j).mapDerivedCategory.obj N)) :=
  let H := ((derivedHom Λ X).obj
    (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N
  let rH := (supportPullback Λ j).mapDerivedCategory.obj H
  let rN := (supportPullback Λ j).mapDerivedCategory.obj N
  (closedSupportOpenDerivedAdjunction Λ j).homEquiv H
    (((derivedHom Λ U).obj (op L)).obj rN)
    ((derivedTensorHomAdjunction Λ L).homEquiv rH rN
      ((openSupportDerivedAdjunction Λ j).homEquiv (((derivedTensor Λ U).obj L).obj rH) N
        (openSupportProjection Λ j L H ≫
          (derivedTensorHomAdjunction Λ
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).counit.app N)))

/-- Closed internal-Hom comparison using an inverse of the canonical closed projection.
Source: proof steps 10 and 11 (blueprint: lem-sfb-open-closed-internal-hom-formulas).
The theorem supplies its inverse projection as an isomorphism with specified hom. -/
noncomputable def closedSupportHomMap {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) (N : DerivedCategory (supportModules Λ X))
    (χ : (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj
          ((supportPullback Λ i).mapDerivedCategory.obj
            (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N))) ⟶
      ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)) :
    (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedHom Λ Z).obj (op P)).obj ((closedSupport Λ i j).rightDerivedFunctor.obj N)) :=
  let H := ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N
  let rH := (supportPullback Λ i).mapDerivedCategory.obj H
  let iN := (closedSupport Λ i j).rightDerivedFunctor.obj N
  (closedPullbackDerivedAdjunction Λ i).homEquiv H
    (((derivedHom Λ Z).obj (op P)).obj iN)
    ((derivedTensorHomAdjunction Λ P).homEquiv rH iN
      ((closedSupportDerivedAdjunction Λ i j hij).homEquiv (((derivedTensor Λ Z).obj P).obj rH) N
        (χ ≫ (derivedTensorHomAdjunction Λ
          ((lowerStar Λ i).mapDerivedCategory.obj P)).counit.app N)))

```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | X6 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | X6, new | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | X6, new | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicIntegralConstantModelCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicRationalConstantModelCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | C7 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.AdicPurityObjects | W9 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | C6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | J7 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | V4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | N3 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | Y5 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.PurityDncInvariance | H2 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.SmoothTrace | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Earlier recorded consumer; no longer downstream in the current scan. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | N1 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| TargetsCheck | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.Statement | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Consumer of the unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Consumer of the unchanged public interface; no adaptation. |

Fresh `tools/downstream.py Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom --names` on 2026-10-19 lists 300 transitive consumers, all recorded above. The direct importers are `Sheaf.Paper.ConstructibleInternalHomContinuity`, `Sheaf.Paper.DetThmSfCtfStabilityInternalHom`, `Sheaf.SixFunctors.ClosedImmersionTensorProjection`, and `Sheaf.SixFunctors.OpenImmersionTensorProjection`. The two tensor-projection modules mention relocated adjunction/projection names; all six relocated declarations retain their original signatures, visibility and bodies through the public maps-module reexport. No consumer source adaptation is necessary.

## Status

landed 20261019T122649-L-482400 2026-10-19 (merge of deliver/X6/Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom)
