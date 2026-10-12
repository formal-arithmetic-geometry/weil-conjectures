module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section
universe u
open CategoryTheory
namespace CategoryTheory

/-- Compatible lifting for a split injective tower along one monomorphism.
The proof is the level-by-level compatible lifting argument of Stacks Project Tag 07KW:
levelwise injectivity extends the first component, and each split transition permits correction
of the next component through its kernel.
(blueprint: lem-pc-injective-split-tower-extension) -/
theorem injective_split_tower_extension (I : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hI : ∀ n : ℕ, Injective (I.obj (Opposite.op n)))
    (hp : ∀ n : ℕ, IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op))
    {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B) [Mono f] (g : A ⟶ I) :
    ∃ h : B ⟶ I, f ≫ h = g := by
  sorry

end CategoryTheory
