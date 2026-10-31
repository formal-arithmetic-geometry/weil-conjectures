/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Upper truncation transfers homology isomorphisms

Source: `WeilConjectures/CategoryTheory/DerivedCategory/CoproductsOfFiniteAmplitude.lean`,
local claim `stepA` in `DerivedCategory.isIso_sigmaComparison_of_bounded`, lines 135–152.
(blueprint: lem-dla1-upper-truncation-homology-transfer)
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory

namespace DerivedCategory

/-- A triangulated functor preserving all lower bounds transfers homology isomorphisms
through degree `m` to a homology isomorphism in degree `m`, when the source is in
canonical degrees at most `m`.

Source: `WeilConjectures/CategoryTheory/DerivedCategory/CoproductsOfFiniteAmplitude.lean`,
`DerivedCategory.isIso_sigmaComparison_of_bounded`, local claim `stepA`, lines 135–152.
(blueprint: lem-dla1-upper-truncation-homology-transfer)

Proof:
1. Complete `f` to a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`. For every `k ≤ m`,
   `H^k(f)` is epi. The map `H^(k+1)(f)` is mono: it is an isomorphism if `k+1 ≤ m`,
   and otherwise its source vanishes because `X.IsLE m`. Apply
   `lem-dla1-triangle-third-homology-zero` to obtain `H^k(Z) = 0`. The standard
   t-structure characterization gives `Z.IsGE (m+1)`.
2. Lower-bound preservation gives `(G.obj Z).IsGE (m+1)`. The functor is triangulated,
   so it sends the chosen triangle to a distinguished triangle. Its third vertex
   has zero homology in degrees `m-1` and `m` by the standard t-structure bounds.
3. Apply `lem-dla1-triangle-homology-map-iso` to these two consecutive vanishings,
   with degrees `m-1` and `m`, to obtain the asserted isomorphism.
-/
theorem isIso_homologyFunctor_map_of_isLE_of_preservesIsGE
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (hG : ∀ (Z : DerivedCategory C) (a : ℤ), Z.IsGE a → (G.obj Z).IsGE a)
    (m : ℤ) {X Y : DerivedCategory C} (f : X ⟶ Y) (hX : X.IsLE m)
    (hf : ∀ (k : ℤ), k ≤ m → IsIso ((homologyFunctor C k).map f)) :
    IsIso ((homologyFunctor D m).map (G.map f)) := by
  sorry

end DerivedCategory
