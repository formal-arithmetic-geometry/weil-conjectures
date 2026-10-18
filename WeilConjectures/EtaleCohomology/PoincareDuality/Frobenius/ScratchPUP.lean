module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section
variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

noncomputable def unitOf (X : Scheme.{u}) : DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))
end

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

set_option maxHeartbeats 3000000 in
lemma e2 {X Y : Scheme.{u}} {a : X ⟶ Y} [IsProper a] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv.app (unitOf (ModuleCat.{u + 1} Λ) X) =
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv.app (𝟙_ (DerivedCategoryModule Λ X)) := rfl

lemma k1 {X Y : Scheme.{u}} {a : X ⟶ Y} [IsProper a] :
    (R(a)_![ModuleCat.{u + 1} Λ]).obj (unitOf (ModuleCat.{u + 1} Λ) X) =
    (R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ X)) := rfl

lemma k2 {X Y : Scheme.{u}} {a : X ⟶ Y} [IsProper a] :
    (R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) =
    (R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ X)) := rfl

end AlgebraicGeometry.Etale
