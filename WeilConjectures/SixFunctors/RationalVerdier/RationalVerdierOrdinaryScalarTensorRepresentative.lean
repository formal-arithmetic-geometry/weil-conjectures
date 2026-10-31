/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierOrdinaryScalarTensorChain
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierScalarCounitModel
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor

/-! # Representative calculations for tensor completion and scalar extension

Source: the normalized completion and tensor calculations in the blueprint proof of
lem-coef-integral-finite-extension, paragraphs 1 and 4.
(blueprint: lem-coef-rational-verdier-ordinary-scalar-tensor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local irreducible] HasDerivedCategory.standard
  integralCompletedTensor integralCompletedTensorComparison
  integralOperationsTensorComplexFunctor integralOrdinaryScalar
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  PurCompactSupport.scalarTensor PurCompactSupport.scalarTensorTotal
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] Functor.mapHomologicalComplex
  completedOrdinaryScalarComplex coefficientTotalTensor
  DerivedCategory.Q DerivedCategory.Qh HomologicalComplexUpToQuasiIso.Qh
  HomotopyCategory.quotient integralOperationsGoodComplex
  IntegralFiniteExtension.tensorModel
attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

private theorem chosen_spec {A : Sort*} {P : A → Prop}
    (h : ∃ a, P a) (a : A) (ha : a = h.choose) : P a :=
  ha.symm ▸ h.choose_spec

private theorem cancel_last {C : Type*} [Category* C]
    {A B C₀ D E F G : C} (f : A ⟶ B) (g : B ⟶ C₀) (h : C₀ ⟶ D)
    (d : A ⟶ E) (e : E ⟶ F) (r : F ⟶ D) (k : D ⟶ G) [Mono k]
    (eq : f ≫ g ≫ h ≫ k = d ≫ e ≫ r ≫ k) : f ≫ g ≫ h = d ≫ e ≫ r := by
  apply (cancel_mono k).mp
  simpa only [Category.assoc] using eq

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (X : Scheme.{u})

set_option maxHeartbeats 600000 in
-- Transport the three representative components across the recorded scalar models.
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- Change the ordinary scalar representative coordinates without changing the
normalized ordinary tensorator. This assertion contains no completion map.
Source: Stacks 03EL, 06YY and 07A4; blueprint
lem-coef-integral-finite-extension.proof.md, paragraph 4.
(blueprint: lem-coef-rational-verdier-ordinary-scalar-tensor-representative).

Proof: scalarTensor is fixed by its flat K-flat representative equation. The
pure-section formula for t identifies the inverse scalarTensorTotal there with
the ordinary tensor chain map, transported by t on each factor and on the total
tensor. Check this on unit scalar homogeneous tensors; both formulas send
1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). The scalar extension
adjunction, sheafification and total tensor coproduct injections extend the
identity to the entire chain map. Substitute the counit equation he on P, Q and
their total tensor into that representative equation. Naturality of the target
representative under the two maps t cancels these maps and gives the displayed
identity. Good source complexes have flat terms and are K-flat, and scalarGood
supplies the displayed good target complexes. No completeness or constructible
inverse is used, including for zero inputs and identity coefficient embeddings. -/
theorem ordinary_scalar_tensor_representative
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (t : integralOrdinaryScalar l E L i X ≅
      completedOrdinaryScalarExtension.{u, u} l E L i X)
    (e : integralOrdinaryDerivedScalar l E L i X ≅
      completedDerivedScalarExtension.{u, u} l E L i X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L i X N U s x) =
        completedScalarTensorSection.{u, u} l E L i X N U s x)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L i X P =
        (integralOrdinaryScalar l E L i X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P))
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (pbcDerivedExtend (completedCoefficientMap l E L i X)).map
        (a.representative.hom.app (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩)) ≫
      (PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
        (IntegralFiniteExtension.tensorModel X a)
        (IntegralFiniteExtension.tensorModel X b)).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      b.tensor.map (Prod.mkHom
        (e.inv.app (DerivedCategory.Q.obj P.obj) ≫
          (integralOrdinaryScalar l E L i X).mapDerivedCategoryFactors.hom.app P.obj)
        (e.inv.app (DerivedCategory.Q.obj Q.obj) ≫
          (integralOrdinaryScalar l E L i X).mapDerivedCategoryFactors.hom.app Q.obj)) =
    (e.inv.app (DerivedCategory.Q.obj ((constructibleTensorTotal l E X).obj (P.obj, Q.obj))) ≫
      (integralOrdinaryScalar l E L i X).mapDerivedCategoryFactors.hom.app
        ((constructibleTensorTotal l E X).obj (P.obj, Q.obj))) ≫
      DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L i X).hom.app (P.obj, Q.obj)) ≫
      b.representative.hom.app
        (⟨_, (scalarGood l E L i X P).1⟩, ⟨_, (scalarGood l E L i X Q).1⟩) := by
  let φ := completedCoefficientMap l E L i X
  change integralOrdinaryScalar l E L i X ≅ pbcExtend φ at t
  change integralOrdinaryDerivedScalar l E L i X ≅ pbcDerivedExtend φ at e
  let F := pbcDerivedExtend φ
  let O := integralOrdinaryScalar l E L i X
  let τ := NatIso.mapHomologicalComplex t (.up ℤ)
  let δ := Functor.whiskerLeft DerivedCategory.Q e.inv ≫ O.mapDerivedCategoryFactors.hom
  let SP : (integralOperationsGoodComplex l L X).FullSubcategory :=
    ⟨_, scalarGood l E L i X P⟩
  let SQ : (integralOperationsGoodComplex l L X).FullSubcategory :=
    ⟨_, scalarGood l E L i X Q⟩
  have hp : proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X) P.obj :=
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).1 P.property.1,
      P.property.2⟩
  have hq : proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X) Q.obj :=
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q.obj).1 Q.property.1,
      Q.property.2⟩
  have hspec := chosen_spec (PurCompactSupport.scalarTensor_existsUnique φ
      (IntegralFiniteExtension.tensorModel X a)
      (IntegralFiniteExtension.tensorModel X b)).exists
    (PurCompactSupport.scalarTensor φ (IntegralFiniteExtension.tensorModel X a)
      (IntegralFiniteExtension.tensorModel X b)) (by unfold PurCompactSupport.scalarTensor; rfl)
  obtain ⟨hp', hq', hμ⟩ := hspec P.obj Q.obj hp hq
  have hε (A : CochainComplex (integralTowerModules l E X) ℤ) :
      pbcComplexCounit φ A = δ.app A ≫ DerivedCategory.Q.map (τ.hom.app A) := by
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [Category.assoc]
    apply (e.app (DerivedCategory.Q.obj A)).eq_inv_comp.mpr
    exact (congrArg (fun z ↦ e.hom.app (DerivedCategory.Q.obj A) ≫ z)
      (ordinary_scalar_counit_model l E L i X A)).trans (he A)
  have htp : IntegralHom.flat.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X)
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P.obj) :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hp'.1
  have htq : IntegralHom.flat.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X)
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q.obj) :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hq'.1
  let vP := (IntegralHom.flat.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l L X)).homMk
      (X := ⟨SP.obj, SP.property.1⟩) (Y := ⟨_, htp⟩) (τ.hom.app P.obj)
  let vQ := (IntegralHom.flat.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l L X)).homMk
      (X := ⟨SQ.obj, SQ.property.1⟩) (Y := ⟨_, htq⟩) (τ.hom.app Q.obj)
  have hn := b.representative.hom.naturality (Prod.mkHom vP vQ)
  change DerivedCategory.Q.map ((constructibleTensorTotal l L X).map
      (Prod.mkHom (τ.hom.app P.obj) (τ.hom.app Q.obj))) ≫
      b.representative.hom.app (⟨_, htp⟩, ⟨_, htq⟩) =
    b.representative.hom.app (⟨SP.obj, SP.property.1⟩, ⟨SQ.obj, SQ.property.1⟩) ≫
      b.tensor.map (Prod.mkHom (DerivedCategory.Q.map (τ.hom.app P.obj))
        (DerivedCategory.Q.map (τ.hom.app Q.obj))) at hn
  have hτ := congrArg DerivedCategory.Q.map
    (ordinary_scalar_tensor_chain l E L i X t ht P.obj Q.obj)
  erw [Functor.map_comp, Functor.map_comp] at hτ
  change F.map (a.representative.hom.app
      (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩)) ≫
      (PurCompactSupport.scalarTensor φ (IntegralFiniteExtension.tensorModel X a)
        (IntegralFiniteExtension.tensorModel X b)).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      b.tensor.map (Prod.mkHom (pbcComplexCounit φ P.obj) (pbcComplexCounit φ Q.obj)) =
    pbcComplexCounit φ ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P.obj Q.obj)
        (PurCompactSupport.scalarTensorTotal_isIso φ P.obj Q.obj)) ≫
      b.representative.hom.app (⟨_, htp⟩, ⟨_, htq⟩) at hμ
  rw [hε, hε, hε] at hμ
  have hprod : Prod.mkHom
      (δ.app P.obj ≫ DerivedCategory.Q.map (τ.hom.app P.obj))
      (δ.app Q.obj ≫ DerivedCategory.Q.map (τ.hom.app Q.obj)) =
    Prod.mkHom (δ.app P.obj) (δ.app Q.obj) ≫
      Prod.mkHom (DerivedCategory.Q.map (τ.hom.app P.obj))
        (DerivedCategory.Q.map (τ.hom.app Q.obj)) := rfl
  rw [hprod, Functor.map_comp] at hμ
  simp only [Category.assoc] at hμ
  erw [reassoc_of% hτ, hn] at hμ
  have hi : IsIso (Prod.mkHom (DerivedCategory.Q.map (τ.hom.app P.obj))
      (DerivedCategory.Q.map (τ.hom.app Q.obj))) := by
    change IsIso (Iso.prod (DerivedCategory.Q.{u + 2}.mapIso (τ.app P.obj))
      (DerivedCategory.Q.{u + 2}.mapIso (τ.app Q.obj))).hom
    infer_instance
  change F.map (a.representative.hom.app
      (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩)) ≫
      (PurCompactSupport.scalarTensor φ (IntegralFiniteExtension.tensorModel X a)
        (IntegralFiniteExtension.tensorModel X b)).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      b.tensor.map (Prod.mkHom (δ.app P.obj) (δ.app Q.obj)) =
    δ.app ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L i X).hom.app (P.obj, Q.obj)) ≫
      b.representative.hom.app (⟨SP.obj, SP.property.1⟩, ⟨SQ.obj, SQ.property.1⟩)
  exact cancel_last _ _ _ _ _ _ _ hμ

end WeilConjectures.RationalVerdier
