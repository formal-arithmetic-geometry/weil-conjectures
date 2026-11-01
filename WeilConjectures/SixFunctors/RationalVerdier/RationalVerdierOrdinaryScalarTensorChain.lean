/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Representative calculations for tensor completion and scalar extension

Source: the normalized completion and tensor calculations in the blueprint proof of
lem-coef-integral-finite-extension, paragraphs 1 and 4.
(blueprint: lem-coef-rational-verdier-ordinary-scalar-tensor-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection completedCoefficientMap
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  PurCompactSupport.scalarTensorTotal
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  HomologicalComplex₂.total Functor.mapBifunctorHomologicalComplex

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] Functor.mapHomologicalComplex
  completedOrdinaryScalarComplex coefficientTotalTensor
attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (X : Scheme.{u})

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem scalar_map_unit
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {A B : pbcModules X R} (f : A ⟶ B) (U : X.ProEtᵒᵖ) (x : A.val.obj U) :
    ((pbcExtend φ).map f).val.app U (pbcTensorSection φ A U 1 x) =
      pbcTensorSection φ B U 1 (f.val.app U x) := by
  have h := congrArg (fun z ↦ z.val.app U x) ((pbcScalarAdjunction φ).unit.naturality f)
  change ((pbcScalarAdjunction φ).unit.app B).val.app U (f.val.app U x) =
    ((pbcExtend φ).map f).val.app U (((pbcScalarAdjunction φ).unit.app A).val.app U x) at h
  erw [(pbcScalarAdjunction_exists φ).exists.choose_spec,
    (pbcScalarAdjunction_exists φ).exists.choose_spec] at h
  exact h.symm

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem scalar_tensor_inverse_pure
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (A B : pbcModules X R) (U : X.ProEtᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (PurCompactSupport.scalarOrdinaryTensor φ A B).inv.val.app U
        (proEtaleTensorPair X S _ _ U
          (pbcTensorSection φ A U 1 x) (pbcTensorSection φ B U 1 y)) =
      pbcTensorSection φ _ U 1 (proEtaleTensorPair X R A B U x y) := by
  have hn := (PurCompactSupport.scalarOrdinaryTensor_existsUnique φ).exists.choose_spec
    A B U 1 x y
  change (PurCompactSupport.scalarOrdinaryTensor φ A B).hom.val.app U
      (pbcTensorSection φ _ U 1 (proEtaleTensorPair X R A B U x y)) = _ at hn
  have h := congrArg (fun z ↦ z.val.app U
      (pbcTensorSection φ _ U 1 (proEtaleTensorPair X R A B U x y)))
    (PurCompactSupport.scalarOrdinaryTensor φ A B).hom_inv_id
  change (PurCompactSupport.scalarOrdinaryTensor φ A B).inv.val.app U
    ((PurCompactSupport.scalarOrdinaryTensor φ A B).hom.val.app U _) = _ at h
  rw [hn] at h
  exact h

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem scalar_tensor_total_pure
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P Q : CochainComplex (pbcModules X R) ℤ) (p q : ℤ)
    (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((PurCompactSupport.scalarTensorTotal φ P Q).f (p + q)).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) S
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)
          p q (p + q) rfl U
          (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y)) =
      pbcTensorSection φ _ U 1
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
          P Q p q (p + q) rfl U x y) := by
  let : (proEtaleOrdinaryTensor X R).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let : ∀ A : pbcModules X R,
      ((proEtaleOrdinaryTensor X R).obj A).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let : (proEtaleOrdinaryTensor X S).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let : ∀ A : pbcModules X S,
      ((proEtaleOrdinaryTensor X S).obj A).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  let SP := ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P
  let SQ := ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q
  let a := CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X R)
    p q (p + q) rfl
  let b := CochainComplex.ιMapBifunctor SP SQ (proEtaleOrdinaryTensor X S)
    p q (p + q) rfl
  have hi : b ≫ (PurCompactSupport.scalarTensorTotal φ P Q).f (p + q) =
      (PurCompactSupport.scalarOrdinaryTensor φ (P.X p) (Q.X q)).inv ≫
        (pbcExtend φ).map a := by
    unfold PurCompactSupport.scalarTensorTotal tensorPullbackTotal
      tensorPullbackTotalComponent
    dsimp only [b, CochainComplex.ιMapBifunctor]
    erw [HomologicalComplex.ι_mapBifunctorDesc]
  have h := congrArg (fun z ↦ z.val.app U
    (proEtaleTensorPair X S _ _ U
      (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y))) hi
  change ((PurCompactSupport.scalarTensorTotal φ P Q).f (p + q)).val.app U
      (b.val.app U (proEtaleTensorPair X S _ _ U
        (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y))) =
    ((pbcExtend φ).map a).val.app U
      ((PurCompactSupport.scalarOrdinaryTensor φ (P.X p) (Q.X q)).inv.val.app U _) at h
  change ((PurCompactSupport.scalarTensorTotal φ P Q).f (p + q)).val.app U
      (b.val.app U (proEtaleTensorPair X S _ _ U
        (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y))) =
    pbcTensorSection φ _ U 1 (a.val.app U (proEtaleTensorPair X R _ _ U x y))
  rw [h]
  erw [scalar_tensor_inverse_pure X φ (P.X p) (Q.X q) U x y]
  exact scalar_map_unit X φ a U (proEtaleTensorPair X R _ _ U x y)

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- The two ordinary scalar tensorators agree after the scalar model isomorphism.
This is an equality of chain maps; no derived object or completion occurs.
Source: Stacks 03EL and 07A4; the ordinary tensor calculation in blueprint
lem-coef-integral-finite-extension.proof.md, paragraph 4.
(blueprint: lem-coef-rational-verdier-ordinary-scalar-tensor-chain).

Proof: apply the scalar extension adjunction in each degree and test on every
homogeneous tensor generator. The formula for t sends the unit scalar tensor
to the same unit scalar tensor in the other sheafified scalar model. The two
ordinary tensorators then both send 1 tensor (x tensor y) to the tensor of
1 tensor x and 1 tensor y. Naturality of t moves each coproduct injection past
its component on the total tensor. The ordinary tensorator's inverse formula
multiplies its scalar factors, so this verifies the displayed orientation too.
Sheafification and the total-tensor coproduct injections detect equality in
each degree. Chain-map extensionality finishes. The argument works without
flatness or boundedness and includes zero complexes and identity embeddings. -/
theorem ordinary_scalar_tensor_chain
    (t : integralOrdinaryScalar l E L i X ≅
      pbcExtend (completedCoefficientMap l E L i X))
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L i X N U s x) =
        pbcTensorSection (completedCoefficientMap l E L i X) N U s x)
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app
        ((constructibleTensorTotal l E X).obj (P, Q)) ≫
      @inv _ _ _ _
        (PurCompactSupport.scalarTensorTotal (completedCoefficientMap l E L i X) P Q)
        (PurCompactSupport.scalarTensorTotal_isIso (completedCoefficientMap l E L i X) P Q) =
    (scalarOrdinaryTensorChain l E L i X).hom.app (P, Q) ≫
      (constructibleTensorTotal l L X).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app Q)) := by
  let φ := completedCoefficientMap l E L i X
  let τ : (integralOrdinaryScalar l E L i X).mapHomologicalComplex (.up ℤ) ≅
      (pbcExtend φ).mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex t (.up ℤ)
  let κ := PurCompactSupport.scalarTensorTotal φ P Q
  let hκ : IsIso κ := PurCompactSupport.scalarTensorTotal_isIso φ P Q
  change τ.hom.app ((constructibleTensorTotal l E X).obj (P, Q)) ≫
      @inv _ _ _ _ κ hκ =
    (scalarOrdinaryTensorChain l E L i X).hom.app (P, Q) ≫
      (constructibleTensorTotal l L X).map
        (Prod.mkHom (τ.hom.app P) (τ.hom.app Q))
  apply (cancel_mono κ).mp
  erw [Category.assoc, @IsIso.inv_hom_id _ _ _ _ κ hκ, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalarAdjunction l E L i X).homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u} P Q n
  intro p q hpq U x y
  subst n
  change ((τ.hom.app ((constructibleTensorTotal l E X).obj (P, Q))).f (p + q)).val.app U
      (((scalarAdjunction l E L i X).unit.app _).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl U x y)) =
    (κ.f (p + q)).val.app U
      ((((constructibleTensorTotal l L X).map
        (Prod.mkHom (τ.hom.app P) (τ.hom.app Q))).f (p + q)).val.app U
        ((((scalarOrdinaryTensorChain l E L i X).hom.app (P, Q)).f (p + q)).val.app U
          (((scalarAdjunction l E L i X).unit.app _).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl U x y))))
  erw [scalarAdjunction_unit]
  erw [(scalarOrdinaryTensorChain_existsUnique l E L i X).exists.choose_spec]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}]
  change (t.hom.app _).val.app U (integralOrdinaryTensorSection l E L i X _ U 1 _) =
    (κ.f (p + q)).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l L X) _ _ p q (p + q) rfl U
        ((t.hom.app (P.X p)).val.app U
          (integralOrdinaryTensorSection l E L i X (P.X p) U 1 x))
        ((t.hom.app (Q.X q)).val.app U
          (integralOrdinaryTensorSection l E L i X (Q.X q) U 1 y)))
  erw [ht, ht, ht]
  exact (scalar_tensor_total_pure X φ P Q p q U x y).symm

end WeilConjectures.RationalVerdier
