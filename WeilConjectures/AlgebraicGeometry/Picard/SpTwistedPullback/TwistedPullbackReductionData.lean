/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Coherent reduction of twisted completed pullback

Source: latest blueprint, sec-smooth-purity, integral-adjunction-bijection proof,
Purity paragraph (blueprint: def-sp-twisted-pullback-reduction-data).

Every natural-number index denotes the positive exponent n+1. The target is an
ordinary derived category of strict semilinear systems, including every quotient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite signed Tate line as an entire derived system. Reduction of this flat
completed line gives its ordinary finite quotient at every positive level.
Source: blueprint integral and finite coefficient twists
(blueprint: def-sp-twisted-pullback-reduction-data). -/
def line (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D) (m : ℤ) :
    SpTowerShriek.D l E T :=
  (reduction l E b T D R).obj
    ((DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E T m))

/-- Finite pullback, signed tensor and shift, performed in the entire system category.
The tensor and pullback are the recorded representative-normalized constructions.
Source: blueprint displayed finite source tower
(blueprint: def-sp-twisted-pullback-reduction-data). -/
def finiteSource (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f)
    (DX : SpCoefficientTowersAbelian l E X) (RX : SpReductionTower l E X DX)
    (DY : SpCoefficientTowersAbelian l E Y) (RY : SpReductionTower l E Y DY)
    (m s : ℤ) : sfIntegralConstructibleCategory l E Y ⥤ SpTowerShriek.D l E X :=
  (sfIntegralConstructible l E Y).ι ⋙ reduction l E b Y DY RY ⋙
    SpTowerShriek.pull l E b g ⋙
      Prod.sectL (SpTowerShriek.D l E X) (line l E b X DX RX m) ⋙
        SpTowerShriek.tensor l E b X ⋙ shiftFunctor _ s

/-- Restriction to the positive uniformizer levels e(n+1), in section-preserving
coordinates. All sections, restrictions, and morphisms are fixed, not merely their
isomorphism classes. Source: blueprint cofinal coefficient convention
(blueprint: def-sp-twisted-pullback-reduction-data). -/
structure CofinalModel (b : SpTowerShriek.Base l E) (T : Scheme.{u}) where
  ordinary : coefficientSequenceModules l E T ⥤ SpTowerShriek.S l E T
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]
  sections : ∀ (M : coefficientSequenceModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq ((ordinary.obj M).val.obj (op (n, U.unop)))
      (M.val.obj (op (b.ramification * (n + 1) - 1, U.unop)))
  restrictions : ∀ (M : coefficientSequenceModules l E T)
    {n j : ℕ} (h : j ≤ n) {U V : T.ProEt} (a : U ⟶ V)
    (h' : b.ramification * (j + 1) - 1 ≤ b.ramification * (n + 1) - 1),
    HEq ((ordinary.obj M).val.map (Prod.mkHom (homOfLE h) a).op)
      (M.val.map (Prod.mkHom (homOfLE h') a).op)
  scalars : ∀ (M : coefficientSequenceModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E T n).obj.obj U)
    (a' : (integralCoefficientCommRingSheaf l E T
      (b.ramification * (n + 1) - 1)).obj.obj U)
    (x : (ordinary.obj M).val.obj (op (n, U.unop)))
    (x' : M.val.obj (op (b.ramification * (n + 1) - 1, U.unop))),
    HEq a a' → HEq x x' → HEq (a • x) (a' • x')
  morphisms : ∀ {M N : coefficientSequenceModules l E T} (a : M ⟶ N)
    (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq ((ordinary.map a).val.app (op (n, U.unop)))
      (a.val.app (op (b.ramification * (n + 1) - 1, U.unop)))

attribute [instance] CofinalModel.additive CofinalModel.limits CofinalModel.colimits

/-- The cofinal inverse-image comparison is the mate of the identity on direct-image
sections. This fixes the whole-system comparison before localization.
Source: blueprint restriction to uniformizer levels en
(blueprint: def-sp-twisted-pullback-reduction-data). -/
structure CofinalGeometry (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : SpTowerShriek.Geometry l E b f)
    (FX : CofinalModel l E b X) (FY : CofinalModel l E b Y) where
  direct : finiteSystemPushforward (integralSystemRings l E)
      (integralSystemTransition l E) f ⋙ FY.ordinary ≅ FX.ordinary ⋙ g.push
  direct_sections : ∀ (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((finiteSystemPushforward (integralSystemRings l E)
      (integralSystemTransition l E) f ⋙ FY.ordinary).obj M).val.obj (op (n, U.unop))),
    HEq ((direct.hom.app M).val.app (op (n, U.unop)) x) x
  inverseImage : FY.ordinary ⋙ g.pull ≅
    finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) f ⋙ FX.ordinary
  mate : ∀ M : coefficientSequenceModules l E Y,
    (g.ordinaryAdjunction.homEquiv _ _) (inverseImage.hom.app M) =
      FY.ordinary.map ((finiteSystemAdjunction (integralSystemRings l E)
        (integralSystemTransition l E) f).unit.app M) ≫
      direct.hom.app ((finiteSystemPullback (integralSystemRings l E)
        (integralSystemTransition l E) f).obj M)

/-- Tensor transport along the actual cofinal restriction. The strict ordinary
comparison is the identity on every selected local tensor generator; the general
model fixes its localized class on entire system complexes.
Source: blueprint cofinal restriction; Stacks 07A4
(blueprint: def-sp-twisted-pullback-reduction-data). -/
structure CofinalTensor (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (F : CofinalModel l E b T) where
  comparison : (coefficientDerivedSystemEvaluationCalculus l E T).choose.systemClosed.tensor ⋙
      F.ordinary.mapDerivedCategory ≅
    F.ordinary.mapDerivedCategory.prod F.ordinary.mapDerivedCategory ⋙
      SpTowerShriek.tensor l E b T
  chain : ∀ P Q : CochainComplex (coefficientSequenceModules l E T) ℤ,
    (F.ordinary.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (coefficientSequenceCommRingSheaf l E T)).obj (P, Q)) ≅
      (SemilinearSections.totalTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (SemilinearSections.systemRing (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj
        ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
          (F.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)
  pure : ∀ (P Q : CochainComplex (coefficientSequenceModules l E T) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (b.ramification * (n + 1) - 1, U.unop)))
    (y : (Q.X q).val.obj (op (b.ramification * (n + 1) - 1, U.unop)))
    (x' : (F.ordinary.obj (P.X p)).val.obj (op (n, U.unop)))
    (y' : (F.ordinary.obj (Q.X q)).val.obj (op (n, U.unop)))
    (z : (F.ordinary.obj (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSequenceCommRingSheaf l E T)).obj (P, Q)).X k)).val.obj (op (n, U.unop))),
    HEq x x' → HEq y y' →
    HEq z (coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSequenceCommRingSheaf l E T) P Q p q k hpq
      (op (b.ramification * (n + 1) - 1, U.unop)) x y) →
    (((chain P Q).hom.f k).val.app (op (n, U.unop))) z =
      ((SemilinearSections.tensorSummand.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (SemilinearSections.systemRing (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
        ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq).val.app
          (op (n, U.unop)))
        (SemilinearSections.tensorSection.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (SemilinearSections.systemRing (Scheme.ProEt.topology T)
            (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
          (F.ordinary.obj (P.X p)) (F.ordinary.obj (Q.X q)) (op (n, U.unop)) x' y')
  kflat : ∀ P : CochainComplex (coefficientSequenceModules l E T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E T) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := SemilinearSections.systemRing (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  representative : ∀ (P Q : CochainComplex (coefficientSequenceModules l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E T) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E T) Q),
    F.ordinary.mapDerivedCategory.map
        (((coefficientDerivedSystemEvaluationCalculus l E T).choose.systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (coefficientSequenceCommRingSheaf l E T)
          (coefficientDerivedSystemEvaluationCalculus l E T).choose.systemClosed P Q hP hQ).hom) ≫
      comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    F.ordinary.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (chain P Q).hom ≫
      ((b.calculus T).tensorModels.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (SemilinearSections.systemRing (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
        (b.calculus T).closed _ _ (kflat P hP) (kflat Q hQ)).hom ≫
      (SpTowerShriek.tensor l E b T).map
        (Prod.mkHom (F.ordinary.mapDerivedCategoryFactors.inv.app P)
          (F.ordinary.mapDerivedCategoryFactors.inv.app Q))

/-- Native uniformizer finite source, with the recorded total tensor on entire systems.
Source: blueprint uniformizer-power construction
(blueprint: def-sp-twisted-pullback-reduction-data). -/
def nativeFiniteSource {X Y : Scheme.{u}} (f : X ⟶ Y) (m s : ℤ) :
    sfIntegralConstructibleCategory l E Y ⥤ coefficientSequenceDerived l E X :=
  integralSystemReduction l E Y ⋙
    finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f ⋙
      Prod.sectL (coefficientSequenceDerived l E X)
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj
          ((DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X m))) ⋙
        (coefficientDerivedSystemEvaluationCalculus l E X).choose.systemClosed.tensor ⋙
          shiftFunctor _ s

/-- The native comparison, composed only from the canonical reduction shift,
balanced tensor and completed-pullback comparison. Source: blueprint displayed q
(blueprint: def-sp-twisted-pullback-reduction-data). -/
def nativeComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (m s : ℤ)
    (h : PurReductionLimitShiftData l E X
      (coefficientDerivedSystemEvaluationCalculus l E X).choose)
    (a : (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f ⋙
        (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ≅
      integralSystemReduction l E Y ⋙ finiteSystemDerivedPullback
        (integralSystemRings l E) (integralSystemTransition l E) f)
    (K : sfIntegralConstructibleCategory l E Y) :
    (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj
        ((source l E f m s).obj K) ≅ (nativeFiniteSource l E f m s).obj K :=
  letI := h.reduction_shift
  let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
  let M := (integralDerivedPullback l E f).obj K.obj
  let L := (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X m)
  (S.reduction.commShiftIso s).app (S.integralClosed.tensor.obj (M, L)) ≪≫
    (shiftFunctor _ s).mapIso
      ((S.reductionTensor.app (M, L)) ≪≫
        S.systemClosed.tensor.mapIso (Iso.prod (a.app K) (Iso.refl _)))

/-- The actual reconstruction composite. The inverse presentation is used solely to
express the same tower in the recorded N_X coordinates; its unit is inserted explicitly.
Source: blueprint final displayed realization
(blueprint: def-sp-twisted-pullback-reduction-data). -/
def realizationMap (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f)
    (DX : SpCoefficientTowersAbelian l E X) (RX : SpReductionTower l E X DX)
    (NX : SpNormalizedEquivalence l E X DX RX)
    (DY : SpCoefficientTowersAbelian l E Y) (RY : SpReductionTower l E Y DY)
    (m s : ℤ)
    (q : source l E f m s ⋙ reduction l E b X DX RX ≅
      finiteSource l E b f g DX RX DY RY m s)
    (C : sfIntegralConstructibleCategory l E Y ⥤
      spNormalizedConstructibleTorTowerCategory l E X DX)
    (v : finiteSource l E b f g DX RX DY RY m s ≅
      C ⋙ (spNormalizedConstructibleTorTowers l E X DX).ι ⋙
        (spTowerShriekRealization l E b X DX).functor)
    (K : sfIntegralConstructibleCategory l E Y) :
    letI := NX.forgetAdditive
    letI := NX.forgetLimits
    letI := NX.forgetColimits
    (source l E f m s).obj K ⟶
      (spCompletedTotalLimit l E X DX).obj (C.obj K).obj :=
  letI := NX.forgetAdditive
  letI := NX.forgetLimits
  letI := NX.forgetColimits
  let H := (spTowerShriekRealization l E b X DX)
  NX.adjunction.unit.app ((source l E f m s).obj K) ≫
      (spCompletedTotalLimit l E X DX).map
        (H.unitIso.hom.app ((spCompletedReduction l E X DX RX).obj
            ((source l E f m s).obj K)) ≫
          H.inverse.map (q.hom.app K ≫ v.hom.app K) ≫
            H.unitIso.inv.app (((C ⋙
              (spNormalizedConstructibleTorTowers l E X DX).ι).obj K)))

/-- The canonical signed line reduction, including the first power's quotient-unit
formula, zero unit, positive balancing and negative dual-evaluation normalization.
Source: blueprint Tate coefficient comparisons; Stacks 03EK, 07A4
(blueprint: def-sp-twisted-pullback-reduction-data). -/
structure TateReduction (T : Scheme.{u}) where
  first : ∀ n : ℕ,
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (Scheme.purTwistIntegralModule T l E) ≅ Scheme.purTwistFiniteOne T l E n
  first_unit : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (Scheme.purTwistIntegralModule T l E).val.obj U),
    (first n).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (completedIntegralCommRingProjectionUnrestricted l E T n)
        (Scheme.purTwistIntegralModule T l E) U 1 x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (Scheme.purTwistIntegralQuotient T l E n)
        (Scheme.purTwistIntegralOne T l E) U 1 x
  signed : ∀ (n : ℕ) (m : ℤ),
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (integralTwistLine l E T m) ≅ finiteCoefficientTwist l E T n m
  signed_normalized : ∀ n : ℕ,
    SheafOfModules.SignedLineComparisonNormalized.{u + 1, u, u + 1}
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (Scheme.purTwistIntegralModule T l E) (Scheme.purTwistFiniteOne T l E n)
      (first n) (signed n)
  ordinary : ∀ (n : ℕ) (m : ℤ),
    (scalarReductionExtension l E T n).obj (integralTwistLine l E T m) ≅
      finiteCoefficientTwist l E T n m
  ordinary_normalized : ∀ (n : ℕ) (m : ℤ) (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (x : (integralTwistLine l E T m).val.obj U),
    (ordinary n m).hom.val.app U
      (sfReductionTensor l E T n (integralTwistLine l E T m) U a x) =
      (signed n m).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (completedIntegralCommRingProjectionUnrestricted l E T n)
          (integralTwistLine l E T m) U a x)
  kflat : ∀ m : ℤ, CochainComplex.IsKFlatIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E T)
    ((CochainComplex.singleFunctor _ 0).obj (integralTwistLine l E T m))
  level : ∀ (n : ℕ) (m : ℤ),
    (coefficientSequenceDerivedEvaluation l E T n).obj
      ((coefficientDerivedSystemEvaluationCalculus l E T).choose.reduction.obj
        ((DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E T m))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (finiteCoefficientTwist l E T n m)
  level_formula : ∀ (n : ℕ) (m : ℤ),
    level n m =
      (coefficientSequenceDerivedEvaluation l E T n).mapIso
        ((coefficientDerivedSystemEvaluationCalculus l E T).choose.reduction.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (integralTwistLine l E T m))) ≪≫
      ((coefficientDerivedSystemEvaluationCalculus l E T).choose.reductionEvaluation n).app _ ≪≫
      coefficientFiniteReductionModel l E T _ (kflat m) n ≪≫
      DerivedCategory.Q.mapIso
        (((scalarReductionExtension l E T n).mapCochainComplexSingleFunctor 0).app _ ≪≫
          (CochainComplex.singleFunctor _ 0).mapIso (ordinary n m)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (scalarReductionTarget l E T n) 0).app
        (finiteCoefficientTwist l E T n m)).symm

end WeilConjectures.SpTwistedPullback
