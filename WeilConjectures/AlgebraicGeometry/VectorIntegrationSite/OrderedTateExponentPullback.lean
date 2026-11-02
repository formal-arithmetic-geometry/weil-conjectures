/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ShiftedExponentTransitionPullback
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Pullback of the ordered root transition

Source: finite Tate descent and the canonical Tate identifications in vector integration.
(blueprint: lem-pur-ordered-tate-exponent-pullback)
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open MonoidalCategory
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.rootsOfUnitySheaf Scheme.finiteEtaleTateTwist
  Etale.ordinaryFiniteDegreeZero
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem unit_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K : C} {L : D} (b : F.obj K ⟶ L) :
    F.map (𝟙 K) ≫ b = b ≫ 𝟙 L := by
  calc
    F.map (𝟙 K) ≫ b = 𝟙 (F.obj K) ≫ b :=
      congrArg (fun q ↦ q ≫ b) (F.map_id K)
    _ = b := Category.id_comp b
    _ = b ≫ 𝟙 L := (Category.comp_id b).symm

private theorem tensor_square
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) {K L K' L' : C} {M N M' N' : D}
    (a : K ⟶ K') (b : L ⟶ L') (c : F.obj K' ⟶ M') (d : F.obj L' ⟶ N')
    (e : F.obj K ⟶ M) (g : F.obj L ⟶ N) (i : M ⟶ M') (j : N ⟶ N')
    (δ : F.obj (K ⊗ L) ⟶ F.obj K ⊗ F.obj L)
    (δ' : F.obj (K' ⊗ L') ⟶ F.obj K' ⊗ F.obj L')
    (hn : δ ≫ (F.map a ⊗ₘ F.map b) = F.map (a ⊗ₘ b) ≫ δ')
    (ha : F.map a ≫ c = e ≫ i) (hb : F.map b ≫ d = g ≫ j) :
    F.map (a ⊗ₘ b) ≫ (δ' ≫ (c ⊗ₘ d)) =
      (δ ≫ (e ⊗ₘ g)) ≫ (i ⊗ₘ j) := by
  rw [← Category.assoc, ← hn, Category.assoc, tensorHom_comp_tensorHom, ha, hb]
  rw [← tensorHom_comp_tensorHom, ← Category.assoc]

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
