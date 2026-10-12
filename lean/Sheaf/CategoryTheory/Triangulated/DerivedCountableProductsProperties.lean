module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.CategoryTheory.LocalizationHomColimit

@[expose] public section
universe t w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Termwise product cones are limiting in the derived category and homology
preserves countable discrete limits, once those products exist.
Source: Stacks Project, Derived Categories, Lemma 13.34.2, Tag 07KC.
Exactness of countable products identifies cycles, boundaries and homology of a
termwise product with the corresponding products; localization by
quasi-isomorphisms then transfers the universal property to the derived category.
(blueprint: lem-weil-derived-countable-products-properties) -/
theorem derivedCategory_countableProducts_properties
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts (DerivedCategory A)] :
      (∀ (J : Type t) [Countable J] (C : J → CochainComplex A ℤ),
        Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C))))) ∧
      (∀ (J : Type t) [Countable J] (p : ℤ),
        PreservesLimitsOfShape (Discrete J) (DerivedCategory.homologyFunctor A p)) := by
  sorry

end CategoryTheory
