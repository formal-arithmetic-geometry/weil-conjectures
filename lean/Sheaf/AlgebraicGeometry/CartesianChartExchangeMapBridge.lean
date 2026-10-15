module

public import Sheaf.AlgebraicGeometry.RestrictedOverAbelianComplexData
import Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

lemma restrictedOverCohomologyMap_eq_rawAffine
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k) :
    restrictedOverCohomologyMap k F (p : ℤ) f U =
      rawAffineRestrictedCohomologyMap f.left (B.hom ≫ k) (A.hom ≫ k) w p
        (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app F) U := by
  rfl

end AlgebraicGeometry.Etale
