/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Existence of a map to the derived limit of lower truncations

A complex of modules admits a map to a derived limit of its lower truncations, compatible with
the truncation maps.

## Implementation details

The truncation maps are compatible with the transition maps, so their product map is killed by
`1 - s`, where `s` is the shift on the product; exactness of Hom into the Roos derived-limit
triangle lifts this family. No local cohomology bounds are needed for existence.

## References

* [Stacks Project, Tags 0H72 and 0D62](https://stacks.math.columbia.edu/tag/0H72)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.RingedSpace
/-- Existence part of pointwise truncation reconstruction: the canonical maps from `E` to its
lower truncations lift to a map `c : E ⟶ K` to the derived limit. -/
theorem pointwise_truncation_limit_exists (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (hlocal : ∀ x : X, ∃ (b : ℤ → ℤ) (B : Set (Opens X)),
      (∀ U ∈ B, x ∈ U) ∧
      (∀ V : Opens X, x ∈ V → ∃ U ∈ B, U ≤ V) ∧
      (∀ (m : ℤ) (p : ℕ) (U : Opens X), U ∈ B → b m < (p : ℤ) →
        IsZero ((openModuleCohomology X p U).obj
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X))
            (m - (p : ℤ))).obj E))))
    [HasProduct (fun n : ℕ => (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (π : K ⟶ ∏ᶜ (fun n : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E))
    (δ : (∏ᶜ (fun n : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E) K π δ) :
    (∃ c : E ⟶ K, ∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) := by
  -- Local bounds are needed for the isomorphism part, not for this lift.
  let T : ℕ → DerivedCategory (SheafOfModules.{u} (moduleRings X)) := fun n =>
    (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E
  let f : ∀ n, T (n + 1) ⟶ T n := fun n =>
    (DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E
  let a : E ⟶ ∏ᶜ T := Pi.lift (fun n =>
    (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
  have ha : a ≫ towerTransitionEndomorphism f = 0 := by
    apply Pi.hom_ext
    intro n
    simp [a, towerTransitionEndomorphism, towerProductShift, Category.assoc,
      CategoryTheory.Triangulated.TStructure.π_natTransTruncGEOfLE_app, f, T]
  obtain ⟨c, hc⟩ := Pretriangulated.Triangle.coyoneda_exact₂
    (Pretriangulated.Triangle.mk π (towerTransitionEndomorphism f) δ) hK a ha
  change E ⟶ K at c
  change a = c ≫ π at hc
  refine ⟨c, ?_⟩
  intro n
  rw [← Category.assoc, ← hc]
  exact Pi.lift_comp_π _ n

end AlgebraicGeometry.RingedSpace
