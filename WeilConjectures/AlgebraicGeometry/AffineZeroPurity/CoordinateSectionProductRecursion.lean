/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateAdjunctionComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import Mathlib.GroupTheory.Perm.Sign
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerDescent
import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint latest, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: lem-pur-coordinate-section-product-recursion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

set_option maxRecDepth 2048 in
section CoordinateBaseChangeProof

private theorem transpose_composite
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (F : C ⥤ D) (G : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D') (R' : D' ⥤ C')
    {K R : C} {L : D} {K' : C'} {L' : D'}
    (s : K' ⟶ U.obj K) (θ : K ⟶ R) (m : U.obj R ⟶ R'.obj (V.obj L))
    (t : V.obj L ⟶ L') (ε : F.obj R ⟶ L)
    (ε₀ : G.obj (R'.obj (V.obj L)) ⟶ V.obj L)
    (ε₁ : G.obj (R'.obj L') ⟶ L')
    (eK : G.obj (U.obj K) ⟶ V.obj (F.obj K))
    (eR : G.obj (U.obj R) ⟶ V.obj (F.obj R))
    (a : F.obj K ⟶ L)
    (ha : F.map θ ≫ ε = a)
    (hm : G.map m ≫ ε₀ = eR ≫ V.map ε)
    (hn : G.map (U.map θ) ≫ eR = eK ≫ V.map (F.map θ))
    (ht : G.map (R'.map t) ≫ ε₁ = ε₀ ≫ t) :
    G.map (s ≫ U.map θ ≫ m ≫ R'.map t) ≫ ε₁ =
      G.map s ≫ eK ≫ V.map a ≫ t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ht, reassoc_of% hm, reassoc_of% hn, ← V.map_comp_assoc, ha]

end CoordinateBaseChangeProof

attribute [local irreducible] comparisonUpperStar lowerStar

set_option maxHeartbeats 1000000 in
-- Comparing simultaneous realization witnesses needs a larger elaboration budget.
end AlgebraicGeometry.ProEtale.AffineZeroPurity
