import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open CategoryTheory Limits MonoidalCategory

set_option trace.Meta.synthInstance true in
noncomputable example (C : Type) [Category C] [MonoidalCategory C] :
    MonoidalCategory C := by infer_instance

set_option trace.Meta.synthInstance true in
noncomputable example (A : Type) [Category A] [Abelian A]
    [HasColimitsOfSize.{0,0} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A] :
    MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ)) := by
  infer_instance
