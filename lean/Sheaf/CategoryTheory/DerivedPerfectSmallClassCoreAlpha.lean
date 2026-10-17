module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- The alpha-compact class supplied by the well-generation theorem.

Source: Neeman, Theorem 0.2; Krause, Sections 6.2--6.3.
(blueprint: new-sfb-derived-perfect-small-class-core-alpha)

Proof: choose a regular cardinal above a well-generation bound and above the
compactness ranks of representatives of `P`.  Let `S` be the class of
alpha-compact objects.  Neeman's well-generation theorem and Krause's
cardinal arguments give essential smallness, repleteness, triangulated closure,
closure under coproducts of fewer than `alpha` objects, and alpha-presentability.
The same cardinal bound makes every member of `P` alpha-presentable; this last
fact is recorded separately so that the caller can derive `P ≤ S` by unfolding
`S` rather than hiding that step in the existence theorem.
-/
theorem derived_exists_alphaCompactClass_core
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ (S : ObjectProperty (DerivedCategory A)) (α : Cardinal.{v})
      (_ : Fact α.IsRegular),
      (∀ U, S U ↔ IsCardinalPresentable U α) ∧
      ObjectProperty.EssentiallySmall.{v} S ∧ S.IsClosedUnderIsomorphisms ∧
      S.IsTriangulated ∧
      (∀ (I : Type v) (Y : I → DerivedCategory A),
        HasCardinalLT I α → (∀ i, S (Y i)) → S (∐ Y)) ∧
      (∀ U, S U → IsCardinalPresentable U α) ∧
      (∀ U, P U → IsCardinalPresentable U α) := by
  sorry

end CategoryTheory
