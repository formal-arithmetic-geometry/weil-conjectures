/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7 -/
module

public import Sheaf.Paper.CompletedScalarExactLocalization
public import Sheaf.Paper.ConstantCompletedOrdinaryAssociativity

/-! # Localization of the completed scalar associator

Source: Stacks Tag 07A6, the derived scalar adjunction and its unit normalization.
(blueprint: lem-pur-completed-scalar-associator-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar

/-- The completed scalar associator agrees with exact localization under the
counit-normalized models. Source: Stacks Tag 07A6 (lemma-adjoint)
(blueprint: lem-pur-completed-scalar-associator-localization).
Proof: localize each ordinary scalar adjunction. Conjugate its left functor by
completedTensorModel. On a K-flat complex the resulting unit satisfies precisely
the defining equation of pbcDerivedScalarAdjunction: this follows from
completedTensorModel_counit and the ordinary adjunction unit. Uniqueness in
pbcDerivedScalarAdjunction_exists therefore identifies the two adjunctions.
The ordinary restriction compositor is the identity on sections; its localization
is by definition pbcDerivedRestrictComp. Localization preserves adjunction
composition and transport by this compositor, as follows by their unit formulas.
Finally leftAdjointUniq is characterized by preservation of the unit, so its
localized ordinary instance is the completed derived instance conjugated by the
three exact models. This gives the equation below. All comparisons are natural
and all counits used here are invertible because completedTensor_exact holds;
there are no boundedness, nonzero-object, or nonempty-site assumptions. -/
theorem completedTensorModel_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (j : F →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (haveI := (completedTensor_exact l E F i W).1
     haveI := (completedTensor_exact l E F i W).2
     haveI := (completedTensor_exact l F L j W).1
     haveI := (completedTensor_exact l F L j W).2
     haveI := (completedTensor_exact l E L (j.comp i) W).1
     haveI := (completedTensor_exact l E L (j.comp i) W).2
     haveI := pbcExtend_additive (completedCoefficientMap l E F i W)
     haveI := pbcExtend_additive (completedCoefficientMap l F L j W)
     haveI := pbcExtend_additive (completedCoefficientMap l E L (j.comp i) W)
     (PurCompactSupport.tensorComposition _ _ _
       (PurCompactSupport.completedMap_composition l E F i L j W)).hom.app K ≫
       (completedTensorModel l E L (j.comp i) W).hom.app K =
     (pbcDerivedExtend (completedCoefficientMap l F L j W)).map
       ((completedTensorModel l E F i W).hom.app K) ≫
       (completedTensorModel l F L j W).hom.app
         ((pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory.obj K) ≫
       ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
         Functor.mapDerivedCategoryNatIso
           (ordinaryScalarAssociator _ _ _
             (PurCompactSupport.completedMap_composition l E F i L j W))).hom.app K) := by sorry

end WeilConjectures.PurStrictScalar
