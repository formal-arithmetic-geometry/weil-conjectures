module
public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- Coefficient data on a homogeneous localization.

The coefficient of a homogeneous fraction is defined using the unique scalar relative to
powers of the chosen free generator. Equality of fractions is checked after clearing a
power of the denominator; restricting to the open and using uniqueness proves independence.
The same calculation proves preservation of zero, one, addition, and multiplication, and
proves the displayed numerator equation.
(blueprint: lem-sc-section-ring-coefficient-data). -/
theorem exists_sectionRing_coefficient_data
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d))) :
    ∃ c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U),
      c 0 = 0 ∧ c 1 = 1 ∧
      (∀ a b, c (a + b) = c a + c b) ∧
      (∀ a b, c (a * b) = c a * c b) ∧
      (∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        c (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            ξ.val ξ.property) •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (ξ.val (n • d))) := by sorry
end AlgebraicGeometry.Scheme.Modules
