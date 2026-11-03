/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteAffineScalarCoordinates
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Transposing a normalized scalar Ext square

Source: blueprint finite reduction of purity, Step 4.
(blueprint: lem-pur-finite-scalar-ext-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem shifted_adjunct
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [R.CommShift ℤ] (a : L ⊣ R)
    {X Y : C} {X' Y' : D} (u : L.obj X ≅ X') (v : L.obj Y ⟶ Y')
    (n : ℤ) (c : X ⟶ Y⟦n⟧) :
    a.homEquiv _ _ u.hom ≫
        R.map (u.inv ≫ L.map c ≫
          (Adjunction.LeftAdjointCommShift.iso a n).hom.app Y ≫ v⟦n⟧') ≫
        (R.commShiftIso n).hom.app Y' =
      c ≫ (a.homEquiv _ _ v)⟦n⟧' := by
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, u.hom_inv_id, R.map_id, Category.id_comp]
  rw [a.unit_naturality_assoc]
  rw [Functor.commShiftIso_hom_naturality]
  rw [← reassoc_of% (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso a n Y)]

private theorem insertion_square
    {C D : Type*} [Category C] [Category D]
    [abelianC : Abelian C] [abelianD : Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory C ⥤ DerivedCategory D} (a : L ⊣ R.mapDerivedCategory)
    {X Y : C} {X' Y' : D} (η : X ⟶ R.obj X') (θ : Y ⟶ R.obj Y')
    (u : L.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj X')
    (v : L.obj ((DerivedCategory.singleFunctor C 0).obj Y) ⟶
      (DerivedCategory.singleFunctor D 0).obj Y')
    (hu : u.hom = SheafExactDegreeZero.adjointInsertion R a η)
    (hv : v = SheafExactDegreeZero.adjointInsertion R a θ)
    (n : ℕ) (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    (Ext.mk₀ η).comp
        ((Ext.homEquiv.symm (u.inv ≫ L.map c ≫
          (Adjunction.LeftAdjointCommShift.iso a (n : ℤ)).hom.app _ ≫
            v⟦(n : ℤ)⟧')).mapExactFunctor R) (zero_add n) =
      (Ext.homEquiv.symm c).comp (Ext.mk₀ θ) (add_zero n) := by
  have h := shifted_adjunct a u v (n : ℤ) c
  have hu' : a.homEquiv _ _ u.hom = (DerivedCategory.singleFunctor C 0).map η ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app X' := by
    rw [hu, SheafExactDegreeZero.adjointInsertion, Equiv.apply_symm_apply]
  have hv' : a.homEquiv _ _ v = (DerivedCategory.singleFunctor C 0).map θ ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app Y' := by
    rw [hv, SheafExactDegreeZero.adjointInsertion, Equiv.apply_symm_apply]
  rw [hu', hv'] at h
  have h' := congrArg
    (fun f ↦ f ≫ ((R.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦(n : ℤ)⟧') h
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom,
    ShiftedHom.map, Category.assoc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h'
  rw [← (shiftFunctor (DerivedCategory C) (n : ℤ)).map_comp,
    Iso.inv_hom_id_app] at h'
  dsimp only [Functor.comp_obj] at h'
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    CategoryTheory.Functor.map_id, Category.comp_id, Ext.homEquiv.apply_symm_apply] using h'

private theorem scalar_square
    {C D : Type*} [Category C] [Category D]
    [abelianC : Abelian C] [abelianD : Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory C ⥤ DerivedCategory D} (a : L ⊣ R.mapDerivedCategory)
    {X Y : C} {X' Y' : D} (η : X ⟶ R.obj X') (θ : Y ⟶ R.obj Y')
    (u : L.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj X')
    (v : L.obj ((DerivedCategory.singleFunctor C 0).obj Y) ⟶
      (DerivedCategory.singleFunctor D 0).obj Y')
    (hu : u.hom = SheafExactDegreeZero.adjointInsertion R a η)
    (hv : v = SheafExactDegreeZero.adjointInsertion R a θ)
    (hunit : R.DerivedUnit X X' η) (n : ℕ) (c : Ext X Y n) (c' : Ext X' Y' n)
    (h : (Ext.mk₀ η).comp (c'.mapExactFunctor R) (zero_add n) =
      c.comp (Ext.mk₀ θ) (add_zero n)) :
    L.map c.hom ≫ (Adjunction.LeftAdjointCommShift.iso a (n : ℤ)).hom.app _ ≫
      v⟦(n : ℤ)⟧' = u.hom ≫ c'.hom := by
  have hc := insertion_square R a η θ u v hu hv n c.hom
  simp only [Ext.homEquiv.symm_apply_apply] at hc
  have hinj := (scalar_unit_ext_bijective R (Q := Y') η hunit n).injective
  have he := hinj (h.trans hc.symm)
  have hh := congrArg (fun e : Ext X' Y' n ↦ e.hom) he
  simp only [Ext.hom, Equiv.apply_symm_apply] at hh
  apply (cancel_epi u.inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh.symm

private theorem shifted_single_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    {Y : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {Y' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (θ : Y ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj Y') :
    affineScalarShiftedSingle φ T θ =
      (Adjunction.LeftAdjointCommShift.iso (Etale.purityScalarAdjunction φ T)
        (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj Y) ≫
          (affineScalarSingle φ T θ)⟦(2 : ℤ)⟧' := by
  rfl

set_option maxRecDepth 4096 in
/-- A scalar-unit Ext square gives the actual derived scalar square.
Source: blueprint finite reduction Step 4; Stacks 06YY and 07A6
(blueprint: lem-pur-finite-scalar-ext-square).
Proof: the universal property of the source insertion makes its derived adjunct
invertible. Transpose the conjugated reduced class. The adjunction shift triangle
and the exact-functor single/shift comparisons express its Ext image as the source
insertion followed by restriction of that class. The supplied Yoneda square gives
the same image for the target class. The source scalar unit detects equality on
Ext. Realizing this equality and cancelling the inverse source adjunct gives the
asserted derived scalar square, with no invertibility assumption on the target map. -/
theorem affineScalarSquare_of_extSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    {X Y : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {X' Y' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : X ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj X')
    (θ : Y ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj Y')
    (hη : Etale.SupportedDerivedScalarUnit φ T X X' η)
    (c : Ext X Y 2) (c' : Ext X' Y' 2)
    (h : (Ext.mk₀ η).comp
      (c'.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
      c.comp (Ext.mk₀ θ) (add_zero 2)) :
    (Etale.FiniteSmoothPurity.ordinaryScalar φ T).map c.hom ≫
      affineScalarShiftedSingle φ T θ = affineScalarSingle φ T η ≫ c'.hom := by
  let R := Sheaf.restrictScalars T.smallEtaleTopology φ
  let a := Etale.purityScalarAdjunction φ T
  have hunit := hη
  unfold Etale.SupportedDerivedScalarUnit at hunit
  have hunit' : R.DerivedUnit X X' η := by
    change ∀ N : DerivedCategory _, Function.Bijective (fun f ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app X' ≫ R.mapDerivedCategory.map f)
    exact (SheafExactDegreeZero.scalarUniversal_iff
      T.smallEtaleTopology φ X X' η).mp hunit
  have hgeneric : SheafExactDegreeZero.Universal R η :=
    (SheafExactDegreeZero.universal_iff R η).mpr hunit'
  have hiso : IsIso (SheafExactDegreeZero.adjointInsertion R a η) := by
    exact SheafExactDegreeZero.isIso_adjointInsertion R a η hgeneric
  let u := asIso (SheafExactDegreeZero.adjointInsertion R a η)
  have hθ : affineScalarSingle φ T θ =
      SheafExactDegreeZero.adjointInsertion R a θ := by
    unfold affineScalarSingle SheafExactDegreeZero.adjointInsertion
    rfl
  have hη' : u.hom = SheafExactDegreeZero.adjointInsertion R a η := rfl
  have hh := scalar_square
    (abelianC := Etale.cartierAbelianEtale A T)
    (abelianD := Etale.cartierAbelianEtale B T)
    R a η θ u (affineScalarSingle φ T θ) hη' hθ hunit' 2 c c' h
  have hsource : affineScalarSingle φ T η = u.hom := by
    rw [hη']
    unfold affineScalarSingle SheafExactDegreeZero.adjointInsertion
    rfl
  rw [hsource, shifted_single_eq]
  simpa only [a, Etale.FiniteSmoothPurity.ordinaryScalar, Etale.purityScalarExtension,
    Category.assoc, Nat.cast_ofNat] using hh

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
