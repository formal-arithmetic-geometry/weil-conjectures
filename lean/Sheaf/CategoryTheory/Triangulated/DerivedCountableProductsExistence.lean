module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Existence of countable products in the derived category under exact products.
Source: Stacks Project, Derived Categories, Lemma 13.34.2, Tag 07KC.
The construction takes termwise products of representative complexes and descends
through the derived localization; exactness of products makes products of
quasi-isomorphisms quasi-isomorphisms.
(blueprint: lem-weil-derived-countable-products-existence) -/
theorem derivedCategory_hasCountableProducts
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] :
    HasCountableProducts (DerivedCategory A) := by
  sorry

end CategoryTheory
