module
public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.Algebra.Homology.DoubleComplexVerticalWindow
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
(blueprint: lem-sp-double-complex-vertical-tower-comparison-top)
Proof: construct the cone-to-window comparison from the short exact sequence of smart
truncations columnwise, then totalize the bounded-below quasi-isomorphism and apply homology. -/
theorem verticalTower_interval_homology_iso_top
    (a : ℤ) (n : ℤ) :
    Nonempty ((CochainComplex.mappingCone
      ((verticalTower K).map (homOfLE (show (a : EInt) ≤ ⊤ by simp)))).homology n ≅
      ((total (((ComplexShape.embeddingUpNat.extendFunctor C ⋙
        (ComplexShape.embeddingUpIntGE a).truncGEFunctor C ⋙
        ComplexShape.embeddingUpNat.restrictionFunctor C).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) (ComplexShape.up ℕ)).extend
            ComplexShape.embeddingUpNat).homology n) := by
  sorry
end HomologicalComplex₂
