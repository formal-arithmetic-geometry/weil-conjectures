/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
public import WeilConjectures.SixFunctors.Supporting.Tensor.TotalTensorBraiding
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement

/-! # Total tensor comparisons preserve Koszul braiding

Source: Stacks Tags 06YL and 0FPT; the homogeneous summand calculation.
(blueprint: lem-sf-finite-scalar-tensor-signed-chain).
-/

@[expose] public section
set_option autoImplicit false
universe uC vC uD vD
open CategoryTheory MonoidalCategory
namespace WeilConjectures

/-- An ordinary braided tensor comparison totalizes to the Koszul comparison.
Source: Stacks 06YL and 0FPT.
Proof: on every total-degree summand the comparison is its ordinary component.
Both braidings multiply that summand by the same sign. Additivity carries this
sign through the functor, and the ordinary braiding equation identifies the
remaining composite. Coproduct extensionality proves the equation of chain maps.
(blueprint: lem-sf-finite-scalar-tensor-signed-chain). -/
private theorem forwardSignedChain
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (he : ∀ M N : C, F.map (β_ M N).hom ≫ e.hom.app (N, M) =
      e.hom.app (M, N) ≫ (β_ (F.obj M) (F.obj N)).hom)
    (P Q : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (Q, P) =
      (finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (P, Q) ≫
        (CochainComplex.Monoidal.braiding
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom := by
  have hτ (V W : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n) :
      F.map (HomologicalComplex.ιTensorObj V W p q n h) ≫
          ((finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (V, W)).f n =
        e.hom.app (V.X p, W.X q) ≫ HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj V)
          ((F.mapHomologicalComplex (.up ℤ)).obj W) p q n h := by
    simp only [finiteScalarTotalTensorIsoOfOrdinary, Iso.trans_hom, NatTrans.comp_app,
      finiteScalarUncurryPostcomposeIso_hom_app, Category.id_comp]
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (finiteScalarCurryTensorIso F e).hom (.up ℤ) V W p q n h
  apply HomologicalComplex.hom_ext
  intro n
  change F.map ((CochainComplex.Monoidal.braiding P Q).hom.f n) ≫ _ = _
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro p q h
  change F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ _ =
    F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ _
  rw [← F.map_comp_assoc, CochainComplex.Monoidal.ι_braiding_hom,
    F.map_zsmul, F.map_comp, Preadditive.zsmul_comp, Category.assoc, hτ]
  simp only [HomologicalComplex.comp_f]
  rw [reassoc_of% hτ P Q p q n h]
  rw [CochainComplex.Monoidal.ι_braiding_hom, Preadditive.comp_zsmul]
  erw [reassoc_of% he]
  rfl

/-- The total comparison carries the inverse source swap to the forward target swap.
Source: Stacks 06YL and 0FPT.
Proof: the forward Koszul calculation holds summand by summand. Symmetry of the
source coefficient tensor makes its two Koszul swaps inverse, so the forward
calculation is the stated inverse-source calculation.
(blueprint: lem-sf-finite-scalar-tensor-signed-chain). -/
theorem finiteScalarTensorSignedChain
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [BraidedCategory D]
    [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (he : ∀ M N : C, F.map (β_ M N).hom ≫ e.hom.app (N, M) =
      e.hom.app (M, N) ≫ (β_ (F.obj M) (F.obj N)).hom)
    (P Q : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.Monoidal.braiding Q P).inv ≫
        (finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (Q, P) =
      (finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (P, Q) ≫
        (CochainComplex.Monoidal.braiding
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom := by
  have hinv : (CochainComplex.Monoidal.braiding Q P).inv =
      (CochainComplex.Monoidal.braiding P Q).hom := by
    apply (cancel_mono (CochainComplex.Monoidal.braiding Q P).hom).1
    rw [Iso.inv_hom_id]
    exact (CategoryTheory.RingedDerivedNative.complex_symmetry P Q).symm
  rw [hinv]
  exact forwardSignedChain F e he P Q

attribute [local semireducible] totalTensorBraiding

/-- Any functor carries the signed total square to its target category.
Source: Stacks 06YL and 0FPT.
Proof: apply the functor to the signed chain equation and use preservation of composition.
(blueprint: lem-sf-finite-scalar-tensor-signed-chain). -/
theorem finiteScalarTensorSignedChainMapped
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [BraidedCategory D]
    [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (he : ∀ M N : C, F.map (β_ M N).hom ≫ e.hom.app (N, M) =
      e.hom.app (M, N) ≫ (β_ (F.obj M) (F.obj N)).hom)
    {H : Type*} [Category H] (q : CochainComplex D ℤ ⥤ H)
    (P Q : CochainComplex C ℤ) :
    q.map ((F.mapHomologicalComplex (.up ℤ)).map
        (totalTensorBraiding Q P).inv) ≫
        q.map ((finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (Q, P)) =
      q.map ((finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (P, Q)) ≫
        q.map (totalTensorBraiding
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom := by
  simpa only [q.map_comp, totalTensorBraiding] using
    congrArg q.map (finiteScalarTensorSignedChain F e he P Q)

end WeilConjectures
