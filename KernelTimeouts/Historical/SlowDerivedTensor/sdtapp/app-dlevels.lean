import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open CategoryTheory Limits MonoidalCategory
namespace AlgebraicGeometry
open Scheme
universe u' u

set_option trace.Meta.synthInstance true in
noncomputable def dprimeProviderControl
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] :
    MonoidalCategory (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))) :=
  inferInstance

end AlgebraicGeometry
