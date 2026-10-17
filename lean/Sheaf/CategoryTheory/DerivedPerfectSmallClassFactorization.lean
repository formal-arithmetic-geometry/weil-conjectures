module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Limits.Constructions.Filtered

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Alpha-presentability factors a map to a coproduct through a finite subcoproduct.

Source: Krause, Localization theory, Sections 6.2--6.3. The coproduct is the
filtered colimit of its finite subcoproducts; alpha-presentability gives the required
factorization through one finite stage (which has cardinality less than `α`).
(blueprint: new-sfb-derived-perfect-small-class-factorization)

This is the categorical factorization step used by
`derived_perfectSmallClass_properties`; its proof constructs the filtered
subcoproduct diagram and applies `IsCardinalPresentable.exists_hom_of_isColimit`.
-/
theorem derived_factor_through_small_subcoproduct
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (α : Cardinal.{v}) [Fact α.IsRegular]
    (I : Type v) (Y : I → DerivedCategory A)
    (U : DerivedCategory A) (hU : IsCardinalPresentable U α)
    (f : U ⟶ ∐ Y) :
    ∃ (J : Type v) (_ : Finite J) (a : J → I), HasCardinalLT J α ∧
      ∃ g : U ⟶ ∐ fun j ↦ Y (a j),
        g ≫ Sigma.desc (fun j ↦ Sigma.ι Y (a j)) = f := by
  sorry

end CategoryTheory
