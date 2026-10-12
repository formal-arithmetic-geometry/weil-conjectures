module
public import Sheaf.CategoryTheory.ExactCouple
@[expose] public section
universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
/-- (blueprint: lem-sp-derived-couple-boundary-vanishes)
The image of the incoming alpha maps to zero in the cycle quotient.
This is the boundary calculation in Stacks Tag 011R. -/
theorem derived_couple_boundary_vanishes {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    ∀ p q : ℤ,
      kernel.ι (factorThruImage (X.alpha (p + 1) (q - 1))) ≫
        X.gToCycles (p + 1) (q - 1) ≫
          X.derivedEProjection ((p + 1) + s) ((q - 1) - s) = 0 := by
  sorry
end CategoryTheory.BigradedExactCouple
