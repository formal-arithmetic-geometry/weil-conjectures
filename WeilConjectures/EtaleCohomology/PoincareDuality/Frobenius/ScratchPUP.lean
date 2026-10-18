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

variable {Λ : Type (u + 1)} [CommRing Λ]

lemma e1 {X : Scheme.{u}} (g : X ⟶ X) : unitOf (ModuleCat.{u + 1} Λ) X = 𝟙_ (DerivedCategoryModule Λ X) := rfl

lemma e0 {X : Scheme.{u}} (g : X ⟶ X) : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (unitOf (ModuleCat.{u + 1} Λ) X) ⟶ unitOf (ModuleCat.{u + 1} Λ) X := (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom

variable [Finite Λ]

lemma e2 {X Y : Scheme.{u}} {a : X ⟶ Y} [IsProper a] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv.app (unitOf (ModuleCat.{u + 1} Λ) X) =
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv.app (𝟙_ (DerivedCategoryModule Λ X)) := rfl

lemma e3 {X Y : Scheme.{u}} {a : X ⟶ Y} :
    (R((a)_*[ModuleCat.{u + 1} Λ])).obj (unitOf (ModuleCat.{u + 1} Λ) X) =
    (R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ X)) := rfl

end AlgebraicGeometry.Etale
