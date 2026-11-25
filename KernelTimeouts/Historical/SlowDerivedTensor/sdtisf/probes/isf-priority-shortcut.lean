import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open CategoryTheory Limits MonoidalCategory

attribute [instance 2000] instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
attribute [instance 1000] HomotopyCategory.MonoidalCategory.instMonoidalCategory

set_option trace.Meta.synthInstance true in
noncomputable example (A : Type) [Category A] [Abelian A]
    [HasColimitsOfSize.{0,0} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A] :
    MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ)) := by
  infer_instance
