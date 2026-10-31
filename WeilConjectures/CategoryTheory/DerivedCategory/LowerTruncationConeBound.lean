/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Cone bound from a lower truncation homology isomorphism

Source: `WeilConjectures/CategoryTheory/DerivedCategory/CoproductsOfFiniteAmplitude.lean`,
local stepB, lines 157–170 (blueprint: lem-dla1-lower-truncation-cone-bound).

## Main statements

* `DerivedCategory.isLE_of_isGE_of_isIso_homologyMap` states that the first object of a
  distinguished triangle is in degrees at most `r - 1` when the third object is in degrees at
  least `r` and the second morphism induces cohomology isomorphisms in all degrees at least `r`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Pretriangulated Limits

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/--
Source: `WeilConjectures/CategoryTheory/DerivedCategory/CoproductsOfFiniteAmplitude.lean`,
local stepB, lines 157–170 (blueprint: lem-dla1-lower-truncation-cone-bound).

Proof: For each integer `k ≥ r`, use the long exact cohomology sequence of the
specified distinguished triangle. The map in degree `k` is an isomorphism and hence
monic. The map in degree `k - 1` is an isomorphism when `k ≥ r + 1`; when `k = r`,
its target is zero because `Y.IsGE r`, so it is still epic. Exactness and cancellation
then force the connecting map and the map out of `H^k W` to vanish, and identify the
kernel and image to conclude `H^k W = 0`. Finally `DerivedCategory.isLE_iff` gives
`W.IsLE (r - 1)`.
-/
theorem isLE_of_isGE_of_isIso_homologyMap
    {W X Y : DerivedCategory C} (g : W ⟶ X) (f : X ⟶ Y)
    (h : Y ⟶ W⟦(1 : ℤ)⟧)
    (hT : Triangle.mk g f h ∈ distTriang (DerivedCategory C)) (r : ℤ)
    (hY : Y.IsGE r)
    (hf : ∀ k : ℤ, r ≤ k → IsIso ((homologyFunctor C k).map f)) :
    W.IsLE (r - 1) := by
  rw [isLE_iff]
  intro k hk
  have hkr : r ≤ k := by omega
  let T : Triangle (DerivedCategory C) := Triangle.mk g f h
  have hp : Epi ((homologyFunctor C (k - 1)).map f) := by
    by_cases hkr' : r ≤ k - 1
    · haveI := hf (k - 1) hkr'
      infer_instance
    · have hkr_eq : k = r := by omega
      have hzero : IsZero ((homologyFunctor C (k - 1)).obj Y) := by
        apply isZero_of_isGE Y r (k - 1)
        omega
      exact hzero.epi _
  have hq : Mono ((homologyFunctor C k).map f) := by
    haveI := hf k hkr
    infer_instance
  have hδ : HomologySequence.δ T (k - 1) k (by omega) = 0 := by
    apply (HomologySequence.epi_homologyMap_mor₂_iff T hT (k - 1) k (by omega)).1
    exact hp
  have hg : (homologyFunctor C k).map g = 0 := by
    apply (HomologySequence.mono_homologyMap_mor₂_iff T hT k).1
    exact hq
  have hex := HomologySequence.exact₁ T hT (k - 1) k (by omega)
  exact hex.isZero_X₂ hδ hg

end DerivedCategory
