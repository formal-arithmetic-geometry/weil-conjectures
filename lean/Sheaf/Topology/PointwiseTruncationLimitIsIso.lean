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
/-- Isomorphism part of pointwise truncation reconstruction
(blueprint: lem-pc-ringed-space-pointwise-truncation-limit-isIso).

Proof: fix a compatible map `c`. For each point and cohomological degree, choose a
truncation index beyond the three local bounds supplied by `hlocal`. The successive
truncation triangle and its long exact cohomology sequence make the transitions in the
two adjacent degrees isomorphisms from that index onward. The Roos abelian-group lemma
then kills the resulting `R¹ lim` term. The derived-limit stalk-injectivity lemma,
together with the derived global-sections/limit comparison, shows that the map induced
by `c` on every stalk cohomology group is injective. Its composite with the truncation
map is the canonical truncation isomorphism, so it is also surjective. Isomorphisms on
all stalk cohomology groups imply `IsIso c` by the derived-category cohomology
criterion. This is the uniqueness half of Stacks, Cohomology, Tag 0D62. -/
theorem pointwise_truncation_limit_isIso (X : RingedSpace.{u})
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
    (∀ c : E ⟶ K, (∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) → IsIso c) := by
  sorry

end AlgebraicGeometry.RingedSpace
