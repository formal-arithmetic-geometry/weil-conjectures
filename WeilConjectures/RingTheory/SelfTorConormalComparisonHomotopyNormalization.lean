/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonTateConstruction
import WeilConjectures.RingTheory.KoszulAugmentationLiftHomotopy

/-!
# Homotopy normalization of the self-Tor conormal comparison

A wedge formula for the self-Tor conormal comparison that holds for one augmentation lift of
a Koszul complex holds for every lift.

## References

* [Stacks, Tag 00LS], part (2)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- A wedge formula for one augmentation lift implies the formula for every
lift: a Tate comparison certificate for `c` makes `c` a self-Tor conormal comparison. -/
theorem tate_comparison_homotopy_normalization (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ)
    (c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)))
    (h : TateComparisonCertificate A I n c) :
    IsSelfTorConormalComparison A I n c := by
  intro r g P a ha
  dsimp only
  intro v z hz
  obtain ⟨b, hb, hformula⟩ := h r g P
  obtain ⟨homotopy⟩ := koszul_augmentation_lifts_homotopic A I r g P a b
    (ha.trans hb.symm)
  have heq := ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomotopy homotopy).homologyMap_eq n
  change (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
    (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map a) =
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map b) at heq
  rw [heq]
  exact hformula v z hz

end AlgebraicGeometry
