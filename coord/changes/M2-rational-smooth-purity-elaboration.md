# RationalSmoothPurityCanonical canonical composites

## Reason

Restore the quarantined module after the global-build timeouts in `smallModelIso`
and `commonIso`. The expensive comparisons descend into chosen derived, monoidal,
field, and scalar-localization presentations. Keep these presentations abstract
locally, give composite stages explicit types, and compare the two inherited stage
category structures once. The new helpers are complete constructions/proofs; they
add no proof obligations. Existing theorem statements are preserved, including the
scalar equation; its explicit `FieldComparison.b` arguments only guide elaboration.

## Old

### finiteIntegration

```lean
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y :=
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f
    (AdicSmoothDualizing.levelSetting P n).Coefficient
  (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫
    (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        (((AdicSmoothDualizing.levelSetting P n).diagonalDualizingObject d f
          (Y ↘ Spec (.of P.field.k))).inv ≫
          ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) c).hom.app
            ⟨_, finiteDualizingPlus P f c n d⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
          Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
              (AdicSmoothDualizing.levelSetting P n).Coefficient c
              (HasCompactification.compactification f)).hom.app
                ⟨_, finiteDualizingPlus P f c n d⟩ ≫
              (Etale.rightDerivedUpperShriekAdjunction
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                f).counit.app _))
```

### operation

```lean
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation c s
```

### orientationTrace

```lean
def orientationTrace (d : ℕ)
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0)) :=
  (S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).inv.app _ ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.map a.hom ≫
        (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
```

### smoothPullToOrdinaryOnGood

```lean
def smoothPullToOrdinaryOnGood (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :=
  (integralDerivedPullbackComparison P.coefficients.l P.extension f).app ⟨C,hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C))
      (smoothPullAugmentation_isIso P f d C hC hK)).symm ≪≫
    ((FrobeniusCoefficientTwists.modulePull
      P.coefficients.l P.extension f).mapDerivedCategoryFactors.app C).symm
```

### ordinaryCoefficientUnit

```lean
def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).monoidal.tensorUnit :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm
```

### ordinaryLeftUnitor

```lean
def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
  eqToIso (congrArg (fun a ↦ a.obj ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K))
    (ordinaryModel_existsUnique P.coefficients.l P.extension Y).exists.choose_spec.1) ≪≫
    (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} Y none)
      (IntegralOnSlice.abLocallyBijective.{u, u} Y none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension Y none)).tensor.mapIso
      (Iso.prod (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k))) (Iso.refl K)) ≪≫
    (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} Y none)
      (IntegralOnSlice.abLocallyBijective.{u, u} Y none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension Y none)).monoidal.leftUnitor K
```

### integralTraceTransposeOfOrientation

```lean
def integralTraceTransposeOfOrientation (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.obj
      (integralSource P f d K) ⟶ K :=
  ObjectProperty.homMk
    ((S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).hom.app
        (integralSource P f d K) ≫
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).map (ordinarySource P f d K).hom ≫
      (@asIso _ _ _ _ (projection P f c d K) (projection_isIso P f c d K)).inv ≫
      (ordinaryModel P.coefficients.l P.extension Y).tensor.map
        (Prod.mkHom (orientationTrace P f c S d a) (𝟙 K.obj)) ≫
      (ordinaryLeftUnitor P K.obj).hom)
```

### integralMap

```lean
def integralMap (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ⟶
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
    (integralTraceTranspose P f c S d K)
```

### rationalSourceComparison

```lean
def rationalSourceComparison (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) :=
  (rationalDerivedTensor P.coefficients.l P.extension X).mapIso
    (Iso.prod
      (((sfRationalConstructibleLocalization P.coefficients.l P.extension X).commShiftIso
        (2*(d : ℤ))).symm.app
          (sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ)))
      (Iso.refl _)) ≪≫ eqToIso (rationalIntegralSource_eq P f d K)
```

### rationalIso

```lean
def rationalIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  rationalSourceComparison P f d K ≪≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) X).mapIso
        (integralIso P f c S d (representative P K)) ≪≫
    (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).b.app
      (representative P K) ≪≫
    (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.mapIso
      (eqToIso (representative_eq P K))
```

### smallModelIso

```lean
def smallModelIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :
    (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) f d).obj K ≅
    (S.ring.operation c (.rational
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.obj K :=
  (rationalSource P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) f d).mapIso ((modelRoundtrip P Y).app K).symm ≪≫
    (sourceScalar P.coefficients.l P.extension
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)
      f d ((modelBack P Y).obj K)).symm ≪≫
    (AdicSmoothDualizing.modelScalar P X).mapIso
      (rationalIso P f c S d ((modelBack P Y).obj K)) ≪≫
    (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)).b.app
          ((modelBack P Y).obj K) ≪≫
    (S.ring.operation c (.rational
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.mapIso ((modelRoundtrip P Y).app K)
```

### commonIso

```lean
def commonIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅
      (S.ring.operation c .closed).G.obj K :=
  let e : (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar K.stage) f d).obj K.obj ≅
      (S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage))).G.obj K.obj :=
    smallModelIso (stageSetting P K.stage) f c S d K.obj
  commonSourceComparison P.coefficients.l P.coefficients.Qbar f d K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso e ≪≫
    (S.common.commonComparison c K.stage).b.app K.obj
```

### rationalIso_scalar

```lean
theorem rationalIso_scalar (L : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a X).map (rationalIso P f c S d K).hom ≫
        (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
          (AdicSmoothDualizing.fieldStage (stageSetting P L)) a).b.hom.app K =
      (sourceScalar P.coefficients.l P.extension L.val a f d K).hom ≫
        (rationalIso (stageSetting P L) f c S d
          ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).hom := by
  sorry
```

## New

### finiteIntegration

```lean
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y := by
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f
    (AdicSmoothDualizing.levelSetting P n).Coefficient
  refine (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫ ?_
  refine (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫ ?_
  exact (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        ((@PurityFiniteSetting.diagonalDualizingObject
          (AdicSmoothDualizing.levelSetting P n) X Y d f
          (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
          (inferInstanceAs (QuasiCompact f)) (inferInstanceAs (SmoothOfRelativeDimension d f))
          (Y ↘ Spec (.of P.field.k))
          (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
          (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))).inv ≫
          ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) c).hom.app
            ⟨_, finiteDualizingPlus P f c n d⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
          Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
              (AdicSmoothDualizing.levelSetting P n).Coefficient c
              (HasCompactification.compactification f)).hom.app
                ⟨_, finiteDualizingPlus P f c n d⟩ ≫
              (Etale.rightDerivedUpperShriekAdjunction
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                f).counit.app _))
```

### operation

```lean
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation c s
```

### orientationTrace

```lean
def orientationTrace (d : ℕ)
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0)) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension) c).obj
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj :=
  (S.ring.left c (ConstructibleExceptionalCoefficients.RingStage.integral
      (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).inv.app
      (twist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).F.map a.hom ≫
        (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
```

### smoothPullToOrdinaryOnGood

```lean
def smoothPullToOrdinaryOnGood (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :
    (integralDerivedPullback P.coefficients.l P.extension f).obj (DerivedCategory.Q.obj C) ≅
      (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
        f).obj (DerivedCategory.Q.obj C) :=
  (integralDerivedPullbackComparison P.coefficients.l P.extension f).app ⟨C,hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C))
      (smoothPullAugmentation_isIso P f d C hC hK)).symm ≪≫
    ((FrobeniusCoefficientTwists.modulePull
      P.coefficients.l P.extension f).mapDerivedCategoryFactors.app C).symm
```

### ordinaryCoefficientUnit

```lean
def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (ordinaryClosed P T).monoidal.tensorUnit := by
  unfold ordinaryClosed
  exact (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm
```

### ordinaryTensor_eq and ordinaryLeftUnitor

```lean
theorem ordinaryTensor_eq (T : Scheme.{u}) :
    (ordinaryModel P.coefficients.l P.extension T).tensor = (ordinaryClosed P T).tensor := by
  unfold ordinaryModel ordinaryClosed
  exact uniqueChosen_left _ _
    (ordinaryModel_existsUnique P.coefficients.l P.extension T)

def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
by
  exact tensorLeftUnitorFromPresentation (ordinaryClosed P Y).monoidal
    (ordinaryModel P.coefficients.l P.extension Y).tensor (ordinaryTensor_eq P Y) _ K
    (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k)))

```

### integralTraceTransposeOfOrientation

```lean
def integralTraceTransposeOfOrientation (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).F.obj
      (integralSource P f d K) ⟶ K :=
  ObjectProperty.homMk
    ((S.ring.left c (ConstructibleExceptionalCoefficients.RingStage.integral
      (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).hom.app
        (integralSource P f d K) ≫
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).map (ordinarySource P f d K).hom ≫
      (@asIso _ _ _ _ (projection P f c d K) (projection_isIso P f c d K)).inv ≫
      (ordinaryModel P.coefficients.l P.extension Y).tensor.map
        (Prod.mkHom (orientationTrace P f c S d a) (𝟙 K.obj)) ≫
      (ordinaryLeftUnitor P K.obj).hom)
```

### integralMap

```lean
def integralMap (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ⟶
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
    (integralTraceTranspose P f c S d K)
```

### rationalSourceComparison

```lean
def rationalSourceComparison (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) :=
by
  unfold rationalSource
  exact
    (rationalDerivedTensor P.coefficients.l P.extension X).mapIso
      (Iso.prod
        (((sfRationalConstructibleLocalization P.coefficients.l P.extension X).commShiftIso
          (2*(d : ℤ))).symm.app
            (sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ)))
        (Iso.refl _)) ≪≫ eqToIso (rationalIntegralSource_eq P f d K)
```

### rationalIso

```lean
def rationalIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.rational
        (l := P.coefficients.l)
        (AdicSmoothDualizing.fieldStage P))).G.obj K :=
by
  refine rationalSourceComparison P f d K ≪≫ ?_
  refine (ConstructibleExceptionalCoefficients.rationalization
    P.coefficients.l P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P) X).mapIso
      (integralIso P f c S d (representative P K)) ≪≫ ?_
  refine (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).b.app
    (representative P K) ≪≫ ?_
  exact (operation P f c S (ConstructibleExceptionalCoefficients.Stage.rational
    (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.mapIso
      (eqToIso (representative_eq P K))
```

### smallModelIso

```lean
def smallModelIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :
    (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) f d).obj K ≅
    (S.ring.operation c (ConstructibleExceptionalCoefficients.Stage.rational (l := P.coefficients.l)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.obj K :=
  (rationalSource P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) f d).mapIso ((modelRoundtrip P Y).app K).symm ≪≫
    (sourceScalar P.coefficients.l P.extension
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)
      f d ((modelBack P Y).obj K)).symm ≪≫
    (AdicSmoothDualizing.modelScalar P X).mapIso
      (rationalIso P f c S d ((modelBack P Y).obj K)) ≪≫
    (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)).b.app
          ((modelBack P Y).obj K) ≪≫
    (S.ring.operation c (ConstructibleExceptionalCoefficients.Stage.rational (l := P.coefficients.l)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.mapIso ((modelRoundtrip P Y).app K)
```

### commonIso

```lean
def commonIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅
      (S.ring.operation c .closed).G.obj K :=
by
  have e := smallModelIso (stageSetting P K.stage) f c S d K.obj
  dsimp only [stageSetting, AdicSmoothDualizing.fieldIndex,
    commonModelField, commonModelAlgebra, commonModelFinite] at e
  have e' := transportIsoCategory _ _ (commonCategory_eq P X K.stage) e
  refine commonSourceComparison P.coefficients.l P.coefficients.Qbar f d K ≪≫ ?_
  refine (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) K.stage).mapIso e' ≪≫ ?_
  exact (S.common.commonComparison c K.stage).b.app K.obj
```

### rationalIso_scalar

```lean
theorem rationalIso_scalar (L : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a X).map (rationalIso P f c S d K).hom ≫
        (ConstructibleExceptionalCoefficients.FieldComparison.b
          (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
          (X := X) (Y := Y)
          (s := .rational (AdicSmoothDualizing.fieldStage P))
          (t := .rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
          (A := S.ring.operation c (.rational (AdicSmoothDualizing.fieldStage P)))
          (B := S.ring.operation c
            (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L))))
          (TX := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a X)
          (TY := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y)
          (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a)).hom.app K =
      (sourceScalar P.coefficients.l P.extension L.val a f d K).hom ≫
        (rationalIso (stageSetting P L) f c S d
          ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).hom := by
  sorry
```

Added proved helpers: `tensorLeftUnitorFromPresentation`, `ordinaryClosed`,
`commonCategory_eq`, `transportIsoCategory`, `ordinaryTensor_eq`, and `uniqueChosen_left`. The three local coefficient-model
instances cache the structures already published by `commonField`.

The local reducibility attributes prevent large chosen presentations from unfolding
while assembling maps. The ordinary tensor helper is the same equality transport,
tensor of the unit comparison, and left unitor as the archived body. Common-stage
purity uses the same specialized small-model isomorphism, transported along a proved
equality of category instances before its inclusion. No field, lattice, orientation,
or purity isomorphism is selected from an additional existence statement.

## Users

`tools/downstream.py Sheaf.Paper.RationalSmoothPurityCanonical --uses smallModelIso`
returns `unknown module(s)` because the source is quarantined. Searching live and
quarantined Lean sources finds these six archived direct consumers. They use the
published signatures of the original maps; none unfolds the repaired bodies.
No consumer edit is forced by these definitionally equal interfaces.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | quarantined | Same maps and types. |
| Sheaf.Paper.RationalPurityPresentation | quarantined | Same maps and types. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | quarantined | Same maps and types. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | quarantined | Same maps and types. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | quarantined | Same maps and types. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | quarantined | Same maps and types. |

No target statement or intended definition changes. The canonical factors,
normalizations, and source comparisons are preserved.

## Status

landed 20261025T202559-L-2731123 2026-10-25 (merge of deliver/M2/Sheaf.Paper.RationalSmoothPurityCanonical)
