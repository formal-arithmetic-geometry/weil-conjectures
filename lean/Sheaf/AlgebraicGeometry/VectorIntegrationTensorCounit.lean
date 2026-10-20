/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.AlgebraicGeometry.CompactProjectionExchange
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-! # The coefficient-first tensor-counit mate

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an, Step 7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

open CategoryTheory.MonoidalCategory

private theorem inv_bifunctor_iso_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {T U : C ⥤ D ⥤ E} (e : T ≅ U) (K : C) (L : D) :
    inv ((e.hom.app K).app L) = (e.inv.app K).app L := by
  apply IsIso.inv_eq_of_hom_inv_id
  exact Iso.hom_inv_id ((e.app K).app L)

private theorem bifunctor_tensor_mate
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    (σ : T ≅ T.flip) (τ : U ≅ U.flip)
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (P W : C) (K Q I : D)
    (π : F.obj ((T.obj W).obj P) ⟶ (U.obj Q).obj K)
    (ε : Q ⟶ I) (r : (U.obj K).obj I ⟶ K) (l : (U.obj I).obj K ⟶ K)
    (hu : (τ.inv.app K).app I ≫ r = l) :
    a.homEquiv _ K (F.map ((σ.inv.app W).app P) ≫ π ≫
      (τ.inv.app K).app Q ≫ (U.obj K).map ε ≫ r) =
      (σ.inv.app W).app P ≫
        (a.homEquiv _ _ (π ≫ (U.map ε).app K) ≫ G.map l) := by
  rw [← a.homEquiv_naturality_right, ← a.homEquiv_naturality_left]
  apply congrArg (a.homEquiv _ _)
  have hn := (τ.inv.app K).naturality ε
  simp only [Functor.flip_obj_obj] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, hu]
  rfl

private theorem derived_symmetry_unit
    (C : Type w) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).inv.app K).app (𝟙_ _) ≫
      (ρ_ K).hom = (λ_ K).hom := by
  let := _root_.DerivedCategory.braidedCategory' C
  apply (cancel_epi (β_ K (𝟙_ _)).hom).1
  exact (Iso.hom_inv_id_assoc (β_ K (𝟙_ _)) _).trans
    (braiding_leftUnitor K).symm

private theorem generic_tensor_symmetry_unit
    (A : Type w) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (S : Scheme.{u}) (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    ((derivedTensorSymmetry A S).inv.app K).app (𝟙_ _) ≫
      (derivedTensorRightUnitor A S K).hom = (derivedTensorLeftUnitor A S K).hom := by
  exact @derived_symmetry_unit _ _ _ _ _
    (Etale.sheafMonoidalCategory A S) _ (Etale.sheafBraidedCategory A S)
    (Etale.sheafMonoidalClosed A S) _ K

set_option maxHeartbeats 30000 in
-- Keep the canonical tensor and projection wrappers folded during the mate calculation.
private theorem generic_tensor_counit_adjunct_isIso
    (A : Type w) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [(rightDerivedLowerShriek A f).IsLeftAdjoint] [IsIso (projectionMap A f)]
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (hθ : IsIso (dualizingComplexTensorMapOfIsIso f K)) :
    IsIso ((rightDerivedUpperShriekAdjunction A f).homEquiv _ K
      (inv (((derivedTensorSymmetry A S).hom.app K).app
          ((rightDerivedLowerShriek A f).obj (dualizingComplex A f)) ≫
        ((projectionMap A f).app (dualizingComplex A f)).app K ≫
        (rightDerivedLowerShriek A f).map
          (((derivedTensorSymmetry A X).hom.app (dualizingComplex A f)).app
            ((upperStar A f).leftDerivedFunctor.obj K))) ≫
        ((derivedTensor A S).obj K).map
          ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
        (derivedTensorRightUnitor A S K).hom)) := by
  have hunit := generic_tensor_symmetry_unit A S K
  have heq := bifunctor_tensor_mate (derivedTensor A X) (derivedTensor A S)
    (derivedTensorSymmetry A X) (derivedTensorSymmetry A S)
    (rightDerivedUpperShriekAdjunction A f)
    ((upperStar A f).leftDerivedFunctor.obj K) (dualizingComplex A f) K
    ((rightDerivedLowerShriek A f).obj (dualizingComplex A f)) (𝟙_ _)
    (inv (((projectionMap A f).app (dualizingComplex A f)).app K))
    ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))
    (derivedTensorRightUnitor A S K).hom (derivedTensorLeftUnitor A S K).hom hunit
  simp only [IsIso.inv_comp, ← Functor.map_inv, Category.assoc,
    inv_bifunctor_iso_app]
  erw [heq]
  have ht : IsIso
      ((rightDerivedUpperShriekAdjunction A f).homEquiv _ _
        (inv (((projectionMap A f).app (dualizingComplex A f)).app K) ≫
          ((derivedTensor A S).map
            ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))).app K) ≫
        (rightDerivedUpperShriek A f).map (derivedTensorLeftUnitor A S K).hom) := by
    change IsIso (dualizingComplexTensorMapOfIsIso f K)
    exact hθ
  exact IsIso.comp_isIso'
    (Iso.isIso_inv (((derivedTensorSymmetry A X).app (dualizingComplex A f)).app
      ((upperStar A f).leftDerivedFunctor.obj K))) ht

attribute [local instance 20000] Etale.sheafBraidedCategory

/-- The coefficient-first tensor-counit adjunct is invertible whenever the canonical
orientation-free tensor map is invertible.
Source: the inverse-braiding version of `braided_tensor_mate` in
`Sheaf.AlgebraicGeometry.SmoothTensorDuality`, and blueprint main-20261015,
sec-smooth-purity/sk-prop-an, Step 7.
(blueprint: lem-amb-vector-integration-tensor-counit)

Proof: write F = Rf_!, G = Rf^!, P = Lf^*, w = G(1), and epsilon for the counit.
The coefficient-first projection is beta_{K,Fw} followed by the original projection
pi_{w,K} and F(beta_{w,PK}). Its inverse is therefore F(beta_{w,PK}^{-1}), followed
by pi_{w,K}^{-1} and beta_{K,Fw}^{-1}. Naturality of the inverse braiding identifies
beta_{K,Fw}^{-1} followed by (1_K tensor epsilon) with
(epsilon tensor 1_K) followed by beta_{K,1}^{-1}. The unit-braiding identity sends
beta_{K,1}^{-1} followed by the right unitor to the left unitor. Naturality of the
adjunction Hom equivalence in its source and target therefore identifies the displayed
adjunct with beta_{w,PK}^{-1} followed by the canonical tensor map theta_{f,K}.
Both factors are invertible. This works for every compactifiable f, including the
identity and empty schemes, and requires no smoothness, orientation or bound on K.
The local inverse projection instance in the statement records precisely the inverse
used by the displayed composite; finite projection formula supplies it to consumers.
-/
theorem tensor_counit_adjunct_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (K : DerivedCategoryModule A S)
    [IsIso (compactProjectionMapCoeffFirst A f K (dualizingComplex (ModuleCat A) f))]
    (hθ : IsIso (dualizingComplexTensorMap A f K)) :
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ K
      (inv (compactProjectionMapCoeffFirst A f K (dualizingComplex (ModuleCat A) f)) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app
            (ordinaryFiniteUnit A S)) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom)) := by
  convert (generic_tensor_counit_adjunct_isIso (ModuleCat.{u + 1} A) f K (by
      exact hθ)) using 1 <;> rfl

end AlgebraicGeometry.Etale
