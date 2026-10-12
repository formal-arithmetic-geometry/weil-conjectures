module
public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
/-- Finite/top-endpoint cone comparison, isolating this endpoint case of the
vertical tower comparison.
Source: the columnwise smart truncation and bounded-below totalization argument in Stacks 012X.
(blueprint: lem-sp-double-complex-vertical-tower-comparison-finite)
Proof: construct the cone-to-window comparison from the short exact sequence of smart
truncations columnwise, then totalize the bounded-below quasi-isomorphism and apply homology. -/
theorem verticalTower_interval_homology_iso_finite
    (a b : ℤ) (hab : (a : EInt) ≤ (b : EInt))
    (n : ℤ) :
    Nonempty ((CochainComplex.mappingCone
      ((verticalTower K).map (homOfLE hab))).homology n ≅
      ((total (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).homology n) := by
  sorry
end HomologicalComplex₂
