/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Topology.Category.Profinite.Basic
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTensor

/-! Scalar-counit normalization for the residue pull square.

The tensor presentation on X has already been normalized to its defining counit.
Only the scalar mate and the ordinary balanced tensor comparison occur below.
-/

@[expose] public section

universe v u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

private theorem tensorPresentation_app
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (P : HomotopyCategory (Mod C R) (.up ℤ)) :
    (Mod.tensorPresentationDerivedCounit φ).app P =
      (Mod.comap φ).mapDerivedCategory.map ((Mod.extendScalars φ).leftDerivedFunctorCounit.app P) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((Mod.tensorPresentationHomotopyIso φ).hom.app P) := by
  dsimp only [Mod.tensorPresentationDerivedCounit, Mod.extendComapCounit,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  simp only [DerivedCategory.Qh.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
-- Normalize the inverse scalar mate, retaining ordinary restriction factors.
end AlgebraicGeometry.ProEtale.CondensedRing
