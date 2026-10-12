module

public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Sheaf.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
import Sheaf.Topology.DerivedLimitStalkInjective
import Sheaf.Topology.RingedSpaceRGammaDerivedLimit

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.RingedSpace
/-- Existence part of pointwise truncation reconstruction
(blueprint: lem-pc-ringed-space-pointwise-truncation-limit-exists).

Proof: for each standard lower truncation, use its canonical truncation map from `E`.
These maps are compatible with the transition maps. The product of their differences
is killed by `1 - s`, where `s` is the shift on the product. Exactness of Hom into the
Roos derived-limit triangle lifts this compatible family through `π`, producing a map
`c : E ⟶ K`. The local cohomology bounds imply that the relevant transition maps are
eventual isomorphisms; the Roos abelian-group lemma therefore removes the obstruction in
the derived-limit triangle. This is the existence half of Stacks, Cohomology, Tag 0D62. -/
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
  sorry

end AlgebraicGeometry.RingedSpace
