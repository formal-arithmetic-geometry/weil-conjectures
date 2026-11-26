/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent

/-!
# Vanishing above m gives the m-pseudo-coherent base case

If the cohomology of `C` vanishes in all degrees at least `m`, then `C` is `m`-pseudo-coherent,
witnessed by the zero complex.

## References

* [Stacks, Tag 064W] (part (1))
-/

@[expose] public section

universe w₁ v₁ u₁

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- If all cohomology of `C` in degrees at least `m` vanishes, then `C` is `m`-pseudo-coherent:
the zero complex of finite free modules maps to `C`, inducing isomorphisms on cohomology above
`m` and a surjection in degree `m`. -/
theorem isMPseudoCoherent_of_homology_vanishes {R : Type u₁} [CommRing R]
    [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{v₁} R))
    (hC : ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor (ModuleCat.{v₁} R) i).obj C)) :
    IsMPseudoCoherent m C := by
  open scoped ZeroObject in
  refine ⟨0, 0, 0, inferInstance, inferInstance, ?_, 0, ?_, ?_⟩
  · intro i
    have : Subsingleton ((0 : CochainComplex (ModuleCat.{v₁} R) ℤ).X i) :=
      ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _))
    exact ⟨inferInstance, inferInstance⟩
  · intro i hi
    exact ((homologyFunctor (ModuleCat.{v₁} R) i).map_isZero
      (Q.map_isZero (isZero_zero _))).isIso (hC i (le_of_lt hi)) _
  · exact (hC m le_rfl).epi _

end DerivedCategory
