/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

import all Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink
import Mathlib.CategoryTheory.Whiskering
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Existence of the factorized integral scalar morphism. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.ScalarLocalization.category Padic
  WeilConjectures.sfCompactSupportFiniteFunctor
  WeilConjectures.sfRationalConstructibleLocalization
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
open TensorProduct
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients

/-- Lift a natural transformation and retain its component factorization. -/
private theorem liftFactorization
    {A : Type*} [Category* A] {B : Type*} [Category* B] {C : Type*} [Category* C]
    (S : B ⥤ C) (hS : S.FullyFaithful)
    {F G : A ⥤ B} {H I : A ⥤ C}
    (b : F ⋙ S ≅ H) (d : I ≅ G ⋙ S) (n : H ⟶ I) :
    ∃ tau : F ⟶ G, ∀ K, S.map (tau.app K) =
      b.hom.app K ≫ n.app K ≫ d.hom.app K := by
  let ff := hS.whiskeringRight A
  let m := b.hom ≫ n ≫ d.hom
  refine ⟨ff.preimage m, fun K ↦ ?_⟩
  exact congrArg (fun t ↦ t.app K) (ff.map_preimage m)

variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

set_option allowUnsafeReducibility true in
attribute [local reducible] ScalarLocalization.category
  sfCompactSupportFiniteFunctor sfRationalConstructibleLocalization in
/-- Integral localization commutes with the recorded pure-tensor compact-support action. -/
private def integralLocalizationIso (A : Type u) [Field A] [Algebra (Padic l) A]
    [FiniteDimensional (Padic l) A] :
    sfRationalConstructibleLocalization l A X ⋙ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c A ≅
    sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c A ⋙
        sfRationalConstructibleLocalization l A Y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by
      intro K L h
      dsimp only [Functor.comp_map, Functor.comp_obj, sfCompactSupportFiniteFunctor,
        sfRationalConstructibleLocalization, ScalarLocalization.localization, Iso.refl_hom,
        ScalarLocalization.category]
      simp only [Category.comp_id, Category.id_comp]
      change sfCompactSupportFiniteHomMap l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c A ⟨K⟩ ⟨L⟩
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l A))
            ⊗ₜ[Padic.coefficientExtensionIntegers l A] h) =
        (1 : Localization.Away (Padic.coefficientExtensionUniformizer l A))
          ⊗ₜ[Padic.coefficientExtensionIntegers l A]
          (sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c A).map h
      exact LinearMap.baseChange_tmul _ _ _)

section StageBridge
attribute [local irreducible] Padic.coefficientExtensionIntegers
  ScalarLocalization.preadditive ScalarLocalization.linear
  sfIntegralConstructibleLinear integralCoefficientLinear
  Linear.homModule Preadditive.homGroup
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage category Shrink.instField Shrink.instAlgebra
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

set_option maxHeartbeats 1000000 in
-- Matching the cached and raw coefficient categories exceeds the default heartbeat count.
-- The complete file still compiles within the project's 60-second limit.
/-- The finite-stage action is isomorphic to the recorded rational action. -/
private def rationalStageIso (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l)) :
    stage.system.Φ E ≅ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient.{u} l (PadicAlgCl l) E) :=
  eqToIso (eq_of_heq (stage.finite E)) ≪≫ P.ring.rationalLeft c (finiteField l E)
end StageBridge

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory category
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

abbrev finiteSourceAux (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l)) :=
  GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J

abbrev finiteTargetAux (source : Realization l X)
    (E : Index l (PadicAlgCl l)) :=
  GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c

/--
The geometric construction of the integral scalar morphism, retaining only its
natural transformation and the two outer-factor decomposition. The remaining
six-arrow normalization is stated separately in
`NativeCompactSupportIntegralScalarMorphismNormalization`.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-integral-scalar-morphism-existence).
-/
theorem native_integral_scalar_morphism_exists [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : ∀ E, (change E).map X = (source.coefficient E).integralMap l X)
    (ht : ∀ E, (change E).map Y = (target.coefficient E).integralMap l Y)
    (E : Index l (PadicAlgCl l)) :
    ∃ tau : sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        finiteSourceAux l D hl P c target stage E ⟶
      sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        finiteTargetAux l c source E,
      ∀ K : finiteTorConstructibleIntegralCategory l
          (Coefficient l (PadicAlgCl l) E) X,
        ∃ (b : (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient l (PadicAlgCl l) E) X ⋙
                finiteSourceAux l D hl P c target stage E).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient l (PadicAlgCl l) E) X).obj K)) ≅
            (PurCompactSupport.image (PurCompactSupport.completed l
              (Coefficient l (PadicAlgCl l) E)) c ⋙
              pbcDerivedExtend ((change E).map Y)).obj K.obj)
          (d : (pbcDerivedExtend ((change E).map X) ⋙
              PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ≅
            (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient l (PadicAlgCl l) E) X ⋙
                finiteTargetAux l c source E).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient l (PadicAlgCl l) E) X).obj K))),
          (sections l Y).mapDerivedCategory.map
              (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K)) =
            b.hom ≫ (PurCompactSupport.comparison (change E) c).app K.obj ≫ d.hom := by
  let A := Coefficient.{u} l (PadicAlgCl l) E
  let : Category (sfRationalConstructibleCategory l A X) :=
    GeneralAlgebraicallyClosedCoefficients.stageCategory l (PadicAlgCl l) X E
  let : Category (sfRationalConstructibleCategory l A Y) :=
    GeneralAlgebraicallyClosedCoefficients.stageCategory l (PadicAlgCl l) Y E
  let QX : sfIntegralConstructibleCategory l A X ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E :=
    sfRationalConstructibleLocalization l A X
  let QY : sfIntegralConstructibleCategory l A Y ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) Y E :=
    sfRationalConstructibleLocalization l A Y
  let IX := (sfIntegralConstructible l A X).ι
  let iX := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let iY := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := Y) E
  let FI := sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c A
  let FR : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) Y E :=
    sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c A
  let SY := (sections l Y).mapDerivedCategory
  let CY := pbcDerivedExtend ((change E).map Y)
  let CX := pbcDerivedExtend ((change E).map X)
  let erational : stage.system.Φ E ≅ FR := rationalStageIso l D hl P c stage E
  let a : iX ⋙ stage.system.functor ≅ FR ⋙ iY :=
    stage.system.ιCompFunctorIso E ≪≫ Functor.isoWhiskerRight erational iY
  let q : QX ⋙ FR ≅ FI ⋙ QY := integralLocalizationIso l D hl c A
  let ey : pbcDerivedExtend ((target.coefficient E).integralMap l Y) ≅ CY :=
    eqToIso (congrArg pbcDerivedExtend (ht E).symm)
  let ex : CX ≅ pbcDerivedExtend ((source.coefficient E).integralMap l X) :=
    eqToIso (congrArg pbcDerivedExtend (hs E))
  let b : (QX ⋙ finiteSourceAux l D hl P c target stage E) ⋙ SY ≅
      IX ⋙ PurCompactSupport.image (PurCompactSupport.completed l A) c ⋙ CY :=
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft QX (Functor.isoWhiskerRight a target.J)) SY ≪≫
      Functor.isoWhiskerRight q (iY ⋙ target.J ⋙ SY) ≪≫
      Functor.isoWhiskerLeft FI (target.integral E) ≪≫
      Functor.isoWhiskerRight
        (sfQcqsCompactSupportRealization l A D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).symm
        (pbcDerivedExtend ((target.coefficient E).integralMap l Y)) ≪≫
      Functor.isoWhiskerLeft
        (IX ⋙ PurCompactSupport.image (PurCompactSupport.completed l A) c) ey
  let d : IX ⋙ CX ⋙ PurCompactSupport.image (nativeCoefficients l) c ≅
      (QX ⋙ finiteTargetAux l c source E) ⋙ SY :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft IX ex)
        (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
      Functor.isoWhiskerRight (source.integral E).symm
        (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
      Functor.isoWhiskerLeft (QX ⋙ iX ⋙ source.J) (operationTransport l c).symm
  obtain ⟨tau, htau⟩ := liftFactorization SY (Functor.FullyFaithful.ofFullyFaithful SY)
    b d (Functor.whiskerLeft IX (PurCompactSupport.comparison (change E) c))
  refine ⟨tau, ?_⟩
  intro K
  let K' := (PurCompactSupport.finiteTorIntegralInclusion l A X).obj K
  exact ⟨b.app K', d.app K', htau K'⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
