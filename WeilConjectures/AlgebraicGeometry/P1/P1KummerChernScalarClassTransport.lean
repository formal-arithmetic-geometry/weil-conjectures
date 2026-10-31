/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpoints
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Ordinary class transport under normalized scalar extension

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: the Kummer classes over B are images
from residue coefficients; normalized unit and Tate-line comparisons
(blueprint: lem-sp-p1-kummer-chern-class-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

/-- The underlying additive map of the normalized line insertion.
Source: blueprint latest,
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md,
Charts: Kummer classes over B are images from residue coefficients
(blueprint: lem-sp-p1-kummer-chern-class-transport). -/
def p1KummerScalarForgetLineMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0}
    {hB : (N : B) = 0} {T : Scheme.{u}}
    (e : P1KummerScalarEndpoints φ N hA hB T) :
    (moduleAbelianForget A T).obj (Scheme.finiteEtaleTateLine T N A hA) ⟶
      (moduleAbelianForget B T).obj (Scheme.finiteEtaleTateLine T N B hB) := by
  exact (moduleAbelianForget A T).map e.lineInsertion

private theorem shifted_conjugate_adjunct
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [R.CommShift ℤ] (a : L ⊣ R)
    {X Y : C} {X' Y' : D} (u : L.obj X ≅ X') (v : L.obj Y ≅ Y')
    (n : ℤ) (c : X ⟶ Y⟦n⟧) :
    a.homEquiv _ _ u.hom ≫
        R.map (u.inv ≫ L.map c ≫
          (Adjunction.LeftAdjointCommShift.iso a n).hom.app Y ≫ v.hom⟦n⟧') ≫
        (R.commShiftIso n).hom.app Y' =
      c ≫ (a.homEquiv _ _ v.hom)⟦n⟧' := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, u.hom_inv_id, R.map_id, Category.id_comp]
  rw [a.unit_naturality_assoc]
  rw [Functor.commShiftIso_hom_naturality]
  rw [← reassoc_of% (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso a n Y)]

private theorem insertion_ext_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory C ⥤ DerivedCategory D} (a : L ⊣ R.mapDerivedCategory)
    {X Y : C} {X' Y' : D} (η : X ⟶ R.obj X') (θ : Y ⟶ R.obj Y')
    (u : L.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj X')
    (v : L.obj ((DerivedCategory.singleFunctor C 0).obj Y) ≅
      (DerivedCategory.singleFunctor D 0).obj Y')
    (hu : u.hom = SheafExactDegreeZero.adjointInsertion R a η)
    (hv : v.hom = SheafExactDegreeZero.adjointInsertion R a θ)
    (n : ℕ) (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    (Ext.mk₀ η).comp
        ((Ext.homEquiv.symm (u.inv ≫ L.map c ≫
          (Adjunction.LeftAdjointCommShift.iso a (n : ℤ)).hom.app _ ≫
            v.hom⟦(n : ℤ)⟧')).mapExactFunctor R) (zero_add n) =
      (Ext.homEquiv.symm c).comp (Ext.mk₀ θ) (add_zero n) := by
  have h := shifted_conjugate_adjunct a u v (n : ℤ) c
  have hu' : a.homEquiv _ _ u.hom = (DerivedCategory.singleFunctor C 0).map η ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app X' := by
    rw [hu, SheafExactDegreeZero.adjointInsertion, Equiv.apply_symm_apply]
  have hv' : a.homEquiv _ _ v.hom = (DerivedCategory.singleFunctor C 0).map θ ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app Y' := by
    rw [hv, SheafExactDegreeZero.adjointInsertion, Equiv.apply_symm_apply]
  rw [hu', hv'] at h
  have h' := congrArg
    (fun f ↦ f ≫ ((R.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦(n : ℤ)⟧') h
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom,
    ShiftedHom.map, Category.assoc]
  simp only [Functor.map_comp, Category.assoc] at h'
  rw [← (shiftFunctor (DerivedCategory C) (n : ℤ)).map_comp,
    Iso.inv_hom_id_app] at h'
  dsimp only [Functor.comp_obj] at h'
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    CategoryTheory.Functor.map_id, Category.comp_id,
    Ext.homEquiv.apply_symm_apply] using h'

private theorem integral_generator_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {T : Scheme.{u}} (e : P1KummerScalarEndpoints φ N hA hB T) :
    ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map e.unitInsertion =
      ordinaryFiniteIntegralGenerator B T := by
  let adj := constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [ordinaryFiniteIntegralGenerator, ordinaryFiniteIntegralGenerator]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext x
  change e.unitInsertion.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 T)))
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app _ (x.down : A)) = _
  rw [e.unit_normalization, map_intCast]
  rfl

set_option maxRecDepth 2048 in
/-- The ordinary class is transported by the normalized line insertion.
Source: blueprint latest,
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md,
Charts: Kummer classes over B are images from residue coefficients
(blueprint: lem-sp-p1-kummer-chern-class-transport).

Proof steps:
1. Transpose the conjugate defining `e.chernImage` through scalar adjunction.
2. Use the derived normalization fields and exact-functor composition comparison.
3. Evaluate on the integral constant generator to identify the class map with
`p1KummerScalarForgetLineMap e`. -/
theorem p1KummerChernScalar_class_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0}
    {hB : (N : B) = 0} {T : Scheme.{u}}
    (e : P1KummerScalarEndpoints φ N hA hB T)
    (c : ordinaryFiniteUnit A T ⟶
      (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) :
    ordinaryFiniteClass B T (Scheme.finiteEtaleTateLine T N B hB) 2
        (e.chernImage c) =
      Sheaf.H.map (p1KummerScalarForgetLineMap e) 2
        (ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 c) := by
  let R := Sheaf.restrictScalars T.smallEtaleTopology φ
  let U := moduleAbelianForget A T
  let V := moduleAbelianForget B T
  let x : Ext (ordinaryFiniteConstant A T) (T.finiteEtaleTateLine N A hA) 2 :=
    (ordinaryFiniteExtHomEquiv A T _ _ 2).symm c
  let y : Ext (ordinaryFiniteConstant B T) (T.finiteEtaleTateLine N B hB) 2 :=
    (ordinaryFiniteExtHomEquiv B T _ _ 2).symm (e.chernImage c)
  have hs : (Ext.mk₀ e.unitInsertion).comp (y.mapExactFunctor R) (zero_add 2) =
      x.comp (Ext.mk₀ e.lineInsertion) (add_zero 2) := by
    exact insertion_ext_square R
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
      e.unitInsertion e.lineInsertion e.unitIso e.lineIso
      (by simpa only [p1KummerDerivedInsertion, SheafExactDegreeZero.scalarAdjointInsertion]
        using e.unit_derived)
      (by simpa only [p1KummerDerivedInsertion, SheafExactDegreeZero.scalarAdjointInsertion]
        using e.line_derived) 2 c
  have hf (κ : Ext (ordinaryFiniteConstant B T) (T.finiteEtaleTateLine N B hB) 2) :
      (κ.mapExactFunctor R).mapExactFunctor U = κ.mapExactFunctor V := by
    have h := Ext.mapExactFunctor_comp_mk₀_eq_sheaf R U V (Iso.refl _) κ
    simpa only [Iso.refl_hom, NatTrans.id_app, Ext.comp_mk₀_id,
      Ext.mk₀_id_comp] using h.symm
  have hm := congrArg
    (fun z : Ext (ordinaryFiniteConstant A T) (R.obj (T.finiteEtaleTateLine N B hB)) 2 ↦
      z.mapExactFunctor U) hs
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, hf] at hm
  have hh := congrArg
    (fun z ↦ (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp z (zero_add 2)) hm
  rw [Ext.mk₀_comp_mk₀_assoc, integral_generator_scalar e] at hh
  rw [← Ext.comp_assoc_of_third_deg_zero] at hh
  unfold ordinaryFiniteClass ordinaryFiniteExtClassCore
  rw [Sheaf.H.map_apply]
  exact hh

end AlgebraicGeometry.Etale
