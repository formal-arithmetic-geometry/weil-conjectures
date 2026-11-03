/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.Supporting.Tensor.TotalTensorBraiding
import all WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomDerivedBraiding

/-! # Braiding on native K-flat tensor representatives

Source: Stacks Tags 07A4 and 0FPT.
(blueprint: lem-sf-fixed-tensor-representative-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh

namespace WeilConjectures

attribute [local semireducible] totalTensorBraiding

private theorem invert_commuting
    {D : Type*} [Category D] {A B C E : D}
    (f : A ≅ B) (g : C ≅ E) (b : A ≅ C) (v : B ≅ E)
    (h : b.hom ≫ g.hom = f.hom ≫ v.hom) : g.inv ≫ b.inv = v.inv ≫ f.inv := by
  have he : b ≪≫ g = f ≪≫ v := Iso.ext h
  simpa only [Iso.trans_inv] using congrArg Iso.inv he

universe uA vA wA

attribute [local implicit_reducible] HomotopyCategory.MonoidalCategory.bifunctor
  HomotopyCategory.MonoidalCategory.instMonoidalCategory
  CategoryTheory.Functor.bifunctorMapHomotopyCategory
  CategoryTheory.Quotient.lift₂ HomotopyCategory.quotient

private theorem native_braiding_Q_general
    {C : Type uA} [Category.{vA} C] [Abelian C] [IsGrothendieckAbelian.{vA} C]
    [HasDerivedCategory.{wA} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] (P Q : CochainComplex C ℤ) :
    (DerivedMonoidal.braiding' DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ))
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q Q P =
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
        DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom := by
  let : BraidedCategory (DerivedCategory C) :=
    DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ))
  change (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫ _ = _
  apply braided_ofIso
    ((HomotopyCategory.quotient C (.up ℤ)) ⋙ DerivedCategory.Qh)
    DerivedCategory.Q (DerivedCategory.quotientCompQhIso C)
  intro E H
  have hμ (K L : CochainComplex C ℤ) :
      Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) K L = 𝟙 _ := rfl
  dsimp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map]
  erw [hμ H E, hμ E H]
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact DerivedMonoidal.braiding_hom_μ DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient _ _).obj E) ((HomotopyCategory.quotient _ _).obj H)

/-- Inverse native braiding commutes with the chosen K-flat representative tensorator.
Source: Stacks 07A4 and 0FPT.
Proof: the localization lax tensorator preserves braiding, by transport of the
homotopy-category normalization across quotientCompQhIso. It is invertible on
K-flat pairs. The representative map is its inverse. Invert the normalization
square and substitute these inverse tensorators.
(blueprint: lem-sf-fixed-tensor-representative-braiding). -/
theorem fixedRepresentativeSwapGeneric
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    [HasDerivedCategory.{wA} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    [HasColimitsOfSize.{0, 0} A]
    (S : ObjectProperty (CochainComplex A ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (b : curriedTensor (DerivedCategory A) ≅ (curriedTensor (DerivedCategory A)).flip)
    (hb : ∀ K L, HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding' DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (.up ℤ)) K L).hom)
    (P Q : CochainComplex A ℤ) (hP : S P) (hQ : S Q) :
    (finiteScalarFixedTensorRepresentativeOfKFlat S hS).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
      DerivedCategory.Q.map (totalTensorBraiding Q P).inv ≫
        (finiteScalarFixedTensorRepresentativeOfKFlat S hS).hom.app
          (⟨Q, hQ⟩, ⟨P, hP⟩) := by
  have hb' := eq_of_heq (hb (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P))
  have h := native_braiding_Q_general Q P
  rw [← hb'] at h
  let := finiteScalarLocalizationTensor_isIso Q P (hS _ hP)
  let := finiteScalarLocalizationTensor_isIso P Q (hS _ hQ)
  have hr (Z : S.FullSubcategory × S.FullSubcategory) :
      let := finiteScalarLocalizationTensor_isIso Z.1.obj Z.2.obj (hS _ Z.2.property)
      (finiteScalarFixedTensorRepresentativeOfKFlat S hS).hom.app Z =
        CategoryTheory.inv (Functor.LaxMonoidal.μ DerivedCategory.Q Z.1.obj Z.2.obj) := by
    unfold finiteScalarFixedTensorRepresentativeOfKFlat
    simp only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  rw [hr, hr]
  change ((b.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)).hom ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
    Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
      DerivedCategory.Q.map (totalTensorBraiding Q P).hom at h
  have hi := invert_commuting
    (asIso (Functor.LaxMonoidal.μ DerivedCategory.Q Q P))
    (asIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q))
    ((b.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P))
    (DerivedCategory.Q.mapIso (totalTensorBraiding Q P)) h
  simpa only [asIso_inv, Functor.mapIso_inv, Iso.app_inv] using hi

end WeilConjectures
