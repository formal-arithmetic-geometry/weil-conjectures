/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingComputed
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeOrdinaryPullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedFiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite-free coordinates for the computed scalar pullback comparison

Source: Stacks Project, Tags 03EL, 06YY and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

section CoordinateColumns

universe uA1 vA1 uB1 vB1
open CategoryTheory CategoryTheory.Limits
variable {A : Type uA1} [Category.{vA1} A] [Preadditive A] [HasFiniteBiproducts A]
  {B : Type uB1} [Category.{vB1} B] [Preadditive B] [HasFiniteBiproducts B]
  (d : ℕ)

private theorem powerInjection_naturality {X Y : A} (f : X ⟶ Y) (i : Fin d) :
    biproduct.ι (fun _ : Fin d ↦ X) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫
        (Functor.const (Discrete (Fin d)) ⋙ (lim : (Discrete (Fin d) ⥤ A) ⥤ A)).map f =
      f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom := by
  apply limit.hom_ext
  rintro ⟨j⟩
  change (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫
      (Functor.const (Discrete (Fin d)) ⋙ lim).map f) ≫ Pi.π (fun _ : Fin d ↦ Y) j =
    (f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom) ≫ Pi.π (fun _ : Fin d ↦ Y) j
  simp only [Functor.comp_map, Category.assoc]
  erw [limMap_π]
  change biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ Pi.π _ j ≫ f =
    f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom ≫ Pi.π _ j
  simp only [biproduct.isoProduct_hom, Pi.lift_comp_π]
  erw [Pi.lift_comp_π_assoc]
  by_cases h : i = j <;> simp [h]

private theorem coordinateInjection_naturality (V : A ⥤ A)
    (Φ : V ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    {X Y : A} (f : X ⟶ Y) (i : Fin d) :
    biproduct.ι (fun _ : Fin d ↦ X) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ Φ.inv.app X ≫ V.map f =
      f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom ≫ Φ.inv.app Y := by
  rw [← Φ.inv.naturality f]
  simpa only [Category.assoc] using
    congrArg (fun h ↦ h ≫ Φ.inv.app Y) (powerInjection_naturality d f i)

private theorem powerInjection_map (F : A ⥤ B) [F.Additive]
    (X : A) (i : Fin d) :
    F.map (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom) ≫
      (SheafOfModules.RingedTensor.powerComparison F d).hom.app X =
    biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom := by
  apply limit.hom_ext
  rintro ⟨j⟩
  change _ ≫ Pi.π (fun _ : Fin d ↦ F.obj X) j =
    (biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom) ≫ Pi.π _ j
  rw [Category.assoc, SheafOfModules.RingedTensor.powerComparison_π,
    ← F.map_comp, Category.assoc, biproduct.isoProduct_hom, Pi.lift_comp_π,
    biproduct.isoProduct_hom, Category.assoc, Pi.lift_comp_π]
  by_cases h : i = j <;> simp [h]

private theorem coordinateInjection_square (F : A ⥤ B) [F.Additive]
    (V : A ⥤ A) (V' : B ⥤ B)
    (Φ : V ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ' : V' ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (τ : V ⋙ F ⟶ F ⋙ V')
    (hτ : ∀ X, F.map (Φ.hom.app X) ≫
      (SheafOfModules.RingedTensor.powerComparison F d).hom.app X =
      τ.app X ≫ Φ'.hom.app (F.obj X))
    (X : A) (i : Fin d) :
    F.map (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ Φ.inv.app X) ≫ τ.app X =
    biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom ≫ Φ'.inv.app (F.obj X) := by
  apply (cancel_mono (Φ'.hom.app (F.obj X))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← hτ X, ← Category.assoc, ← F.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  change F.map (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ 𝟙 _) ≫
      (SheafOfModules.RingedTensor.powerComparison F d).hom.app X =
    biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom ≫ 𝟙 _
  simp only [Category.comp_id]
  exact powerInjection_map d F X i

end CoordinateColumns

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
