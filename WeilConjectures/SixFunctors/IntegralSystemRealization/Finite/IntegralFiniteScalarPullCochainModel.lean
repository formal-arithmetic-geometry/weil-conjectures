/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteScalarPullOrdinary
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarPullReductionComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarPullPbcNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarReductionCounitNormalization

/-! # Ordinary and derived finite scalar pullback models

## References

* [Stacks, Tag 0D6D]
* [Stacks, Tag 0D6E]
* [Stacks, Tag 06YY]
* [Stacks, Tag 07A6]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  WeilConjectures.PurCompactSupport.scalarPull
  WeilConjectures.PurCompactSupport.finiteReductionIso
  WeilConjectures.scalarReductionExtension AlgebraicGeometry.Scheme.pbcComplexCounit
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.scalarReductionTargetDerived WeilConjectures.scalarReductionSourceDerived
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Scalar/pullback comparison fixed by the actual restriction/direct-image square.
This is a construction from adjunctions, with no chosen existence witness. -/
@[irreducible] def integralFiniteScalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ringedPull l E f ⋙ scalarReductionDerivedExtension l E X n ≅
      scalarReductionDerivedExtension l E Y n ⋙ finiteDerivedPullback l E n f :=
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let q := PurCompactSupport.scalarPull
    (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f
  Functor.isoWhiskerLeft _ (PurCompactSupport.finiteReductionIso l E X n).symm ≪≫ q ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E Y n) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n f))

/-- On a flat-term K-flat complex the adjunction-normalized derived scalar square
is computed by the ordinary scalar square. -/
theorem integralFiniteScalarPullCochainModel {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (h : integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj)) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    (integralFiniteScalarPull l E f n).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (finiteDerivedPullback l E n f).map
          (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj) =
      (scalarReductionDerivedExtension l E X n).map
          ((integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app P.obj) ≫
        (coefficientFiniteReductionModel l E X
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj) h.1 n).hom ≫
        DerivedCategory.Q.map
          (ordinaryFiniteScalarPullComplex l E f n P.obj) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
            (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)) :=
  by
  let := scalarReductionExtensionAdditive.{u, u} l E X n
  let := scalarReductionExtensionAdditive.{u, u} l E Y n
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let F := integralOrdinaryPull l E f
  let PX : (integralOperationsGoodComplex l E X).FullSubcategory :=
    ⟨(F.mapHomologicalComplex (.up ℤ)).obj P.obj, h⟩
  let fx := F.mapDerivedCategoryFactors.hom.app P.obj
  have hy := finiteScalarPullReductionComparison l E f n P
  have hp := finiteScalarPullPbcNormalization l E f n P.obj
  have hx := finiteScalarReductionCounitNormalization l E X n PX
  have ha := (PurCompactSupport.finiteReductionIso l E X n).hom.naturality fx
  unfold integralFiniteScalarPull
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  apply (cancel_epi ((PurCompactSupport.finiteReductionIso l E X n).hom.app
    ((ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  erw [hy, hp, ← reassoc_of% hx, reassoc_of% ha]

end WeilConjectures.IntegralSystemRealization
