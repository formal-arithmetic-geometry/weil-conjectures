module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization
import Sheaf.CategoryTheory.DerivedPerfectSmallClassFiniteLifting

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
  constructor
  · intro I X Y f hf U hU h
    obtain ⟨J, (_ : Finite J), a, hJ, g, hg⟩ :=
      derived_factor_through_small_subcoproduct α I Y U (hcompact U hU) h
    obtain ⟨q, hq⟩ := (derived_finite_coproduct_surjective I X Y f J a U (fun j ↦
      hf (a j) U hU)) g
    refine ⟨q ≫ Sigma.desc (fun j ↦ Sigma.ι X (a j)), ?_⟩
    change (q ≫ Sigma.desc (fun j ↦ Sigma.ι X (a j))) ≫
      Limits.Sigma.map f = h
    have hmap : Sigma.desc (fun j ↦ Sigma.ι X (a j)) ≫ Limits.Sigma.map f =
        Limits.Sigma.map (fun j ↦ f (a j)) ≫
          Sigma.desc (fun j ↦ Sigma.ι Y (a j)) := by
      apply Sigma.hom_ext
      intro j
      rw [Sigma.ι_desc_assoc]
      rw [Limits.Sigma.ι_map]
      rw [Limits.Sigma.ι_map_assoc]
      rw [Sigma.ι_desc]
    change q ≫ Limits.Sigma.map (fun j ↦ f (a j)) = g at hq
    rw [Category.assoc, hmap, ← Category.assoc, hq, hg]
  · intro I Y hY U hU f
    obtain ⟨J, hfinite, a, hJ, g, hg⟩ :=
      derived_factor_through_small_subcoproduct α I Y U (hcompact U hU) f
    exact ⟨J, a, hSsum J (fun j ↦ Y (a j)) hJ (fun j ↦ hY (a j)), g, hg⟩

end CategoryTheory
