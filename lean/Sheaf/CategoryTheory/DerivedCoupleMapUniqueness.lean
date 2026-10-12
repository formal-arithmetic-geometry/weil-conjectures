module
public import Sheaf.CategoryTheory.ExactCouple
@[expose] public section
universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
/-- (blueprint: lem-sp-derived-couple-map-uniqueness)
The three induced maps are uniquely determined by their descent equations.
This is the universal-property portion of Stacks Tag 011R. -/
theorem derived_couple_map_uniqueness {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    ∃ M : DerivedMaps X,
      (∀ (p q : ℤ) (a : X.derivedD p q ⟶ X.derivedD (p - 1) (q + 1)),
        a ≫ X.derivedDInclusion (p - 1) (q + 1) = X.derivedDInclusion p q ≫ X.alpha p q →
          a = M.alpha p q) ∧
      (∀ (p q : ℤ) (b : X.derivedE p q ⟶ X.derivedD (p + 2) (q - 1)),
        X.derivedEProjection p q ≫ b ≫ X.derivedDInclusion (p + 2) (q - 1) =
            kernel.ι (X.d p q) ≫ X.f p q → b = M.f p q) ∧
      (∀ (p q : ℤ) (c : X.derivedD p q ⟶ X.derivedE (p + (s + 1)) (q - (s + 1))),
        factorThruImage (X.alpha (p + 1) (q - 1)) ≫ c =
            X.gToCycles (p + 1) (q - 1) ≫ X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
              eqToHom (by congr 1 <;> omega) → c = M.g p q) := by
  sorry
end CategoryTheory.BigradedExactCouple
