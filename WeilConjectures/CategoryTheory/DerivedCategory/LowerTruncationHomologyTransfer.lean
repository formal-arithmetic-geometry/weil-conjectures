/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.LowerTruncationConeBound

/-! # Lower truncation transfers homology isomorphisms

Source: `WeilConjectures/CategoryTheory/DerivedCategory/CoproductsOfFiniteAmplitude.lean`,
local claim `stepB` in `DerivedCategory.isIso_sigmaComparison_of_bounded`, lines 154--172.
(blueprint: lem-dla1-lower-truncation-homology-transfer)
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A triangulated functor with upper cohomological amplitude `e` transfers a homology
isomorphism in all degrees at least `m - e` to a homology isomorphism in degree `m`,
when the source and target lie in a replete triangulated class and the target is in
degrees at least `m - e`.

Source: `WeilConjectures/CategoryTheory/DerivedCategory/CoproductsOfFiniteAmplitude.lean`,
local claim `stepB` in `DerivedCategory.isIso_sigmaComparison_of_bounded`, lines 154--172.
(blueprint: lem-dla1-lower-truncation-homology-transfer)

Proof:
1. Complete `f` to a distinguished triangle with `f` as its second arrow by applying
   the cone-triangle clause and rotating backwards. Write the first object as `W`.
2. The cone-bound argument applied with `r = m - e` gives `W.IsLE (m - e - 1)`.
   Rotating the triangle and using the triangulated, replete class hypotheses puts `W`
   in `𝓔`. The amplitude hypothesis therefore gives
   `(G.obj W).IsLE ((m - e - 1) + e)`, hence in particular degrees at most `m - 1`.
3. The triangulated functor sends the triangle to a distinguished triangle. The long
   exact homology sequence has outer terms `H^m(G W)` and `H^(m+1)(G W)`, both zero by
   the preceding bound, so the middle homology map is an isomorphism.
-/
theorem isIso_homologyFunctor_map_of_isGE_of_preservesIsLE
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (𝓔 : ObjectProperty (DerivedCategory C)) [𝓔.IsTriangulated]
    [𝓔.IsClosedUnderIsomorphisms] (e m : ℤ)
    (hG : ∀ (Z : DerivedCategory C) (b : ℤ), 𝓔 Z → Z.IsLE b →
      (G.obj Z).IsLE (b + e))
    {X Y : DerivedCategory C} (f : X ⟶ Y) (hX : 𝓔 X) (hY : 𝓔 Y)
    (hY' : Y.IsGE (m - e))
    (hf : ∀ (k : ℤ), m - e ≤ k → IsIso ((homologyFunctor C k).map f)) :
    IsIso ((homologyFunctor D m).map (G.map f)) := by
  obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle₁ f
  have hW : 𝓔 W := 𝓔.ext_of_isTriangulatedClosed₁ _ hT hX hY
  have hW' : W.IsLE (m - e - 1) := by
    exact isLE_of_isGE_of_isIso_homologyMap g f h hT (m - e) hY' hf
  have hGW := hG W _ hW hW'
  exact isIso_homologyMap_mor₂ _ (G.map_distinguished _ hT) m (m + 1) rfl
    (isZero_of_isLE (G.obj W) (m - e - 1 + e) _ (by lia) (hX := hGW))
    (isZero_of_isLE (G.obj W) (m - e - 1 + e) _ (by lia) (hX := hGW))

end DerivedCategory
