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
import WeilConjectures.Topology.PointwiseTruncationLimitExists
import WeilConjectures.Topology.PointwiseTruncationLimitIsIso

/-! # Pointwise bounds and the derived limit of lower truncations

Local bounds on the cohomology of the cohomology sheaves of a complex of modules imply that the
complex is the derived limit of its lower truncations.

## Implementation details

The compatible map exists by exactness of Hom into the Roos triangle. Under the local bounds, the
transitions of the truncation tower on open cohomology are eventually isomorphisms near every
point, which kills `R¹ lim` and gives injectivity, hence bijectivity, on stalks of cohomology
sheaves.

## References

* [Stacks Project, Tags 0D62 and 0H72](https://stacks.math.columbia.edu/tag/0D62)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Local bounds on the cohomology of the cohomology sheaves imply that every compatible
map to a derived limit of the lower truncations is an isomorphism; such a map exists. -/
theorem pointwise_truncation_limit (X : RingedSpace.{u})
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
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) ∧
    (∀ c : E ⟶ K, (∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) → IsIso c) := by
  constructor
  · exact pointwise_truncation_limit_exists X E hlocal K π δ hK
  · exact pointwise_truncation_limit_isIso X E hlocal K π δ hK

end AlgebraicGeometry.RingedSpace
