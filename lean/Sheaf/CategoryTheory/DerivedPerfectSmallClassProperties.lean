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

/-- Alpha-compactness supplies the perfectness and bounded-subcoproduct clauses.

Source: Krause, Localization theory, Sections 6.2--6.3 and Proposition 6.8.1.
(blueprint: new-sfb-derived-perfect-small-class-properties)

Proof: express a coproduct as the filtered colimit of its subcoproducts with fewer
than `α` summands. The alpha-compact Hom functors commute with that colimit, and
closure of `S` under such subcoproducts gives both displayed conclusions. -/
theorem derived_perfectSmallClass_properties
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (S : ObjectProperty (DerivedCategory A)) (α : Cardinal.{v}) [Fact α.IsRegular]
    [ObjectProperty.EssentiallySmall.{v} S]
    [S.IsClosedUnderIsomorphisms] [S.IsTriangulated]
    (hSsum : ∀ (I : Type v) (Y : I → DerivedCategory A), HasCardinalLT I α →
      (∀ i, S (Y i)) → S (∐ Y))
    (hcompact : ∀ U, S U → IsCardinalPresentable U α) :
    (∀ (I : Type v) (X Y : I → DerivedCategory A) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, S U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) ∧
    (∀ (I : Type v) (Y : I → DerivedCategory A), (∀ i, S (Y i)) →
      ∀ (U : DerivedCategory A), S U → ∀ f : U ⟶ ∐ Y,
      ∃ (J : Type v) (a : J → I), S (∐ fun j ↦ Y (a j)) ∧
        ∃ g : U ⟶ ∐ fun j ↦ Y (a j),
          g ≫ Sigma.desc (fun j ↦ Sigma.ι Y (a j)) = f) := by
  sorry

end CategoryTheory
