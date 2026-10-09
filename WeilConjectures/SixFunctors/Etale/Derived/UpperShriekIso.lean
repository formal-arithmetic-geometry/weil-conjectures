/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The exceptional inverse image along an isomorphism

For an isomorphism of schemes `e : X ≅ Y` the exceptional inverse image is the derived
pullback, `Re^! ≅ Le^*`. Both functors are right adjoint to the same functor: `Re_! ≅ Re_*`
because `e` is proper (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`),
`Re_* ≅ L(e⁻¹)^*` (`AlgebraicGeometry.Etale.rightDerivedLowerStarIsoLeftDerivedUpperStarInv`),
and `L(e⁻¹)^* ⊣ R(e⁻¹)_* ≅ Le^*`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIso`: `Re^! ≅ Le^*`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_eq`: equal morphisms have
  isomorphic exceptional inverse images, whatever the instances of `HasCompactification`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Equal morphisms have isomorphic exceptional inverse images. This transports the
exceptional inverse image along an equation of morphisms, which a rewrite cannot do since the
functor also depends on the `HasCompactification` instance. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] [(R(f)_![A]).IsLeftAdjoint]
    [(R(g)_![A]).IsLeftAdjoint] (h : f = g) :
    Nonempty (R(f)^![A] ≅ R(g)^![A]) := by
  subst h
  exact ⟨Iso.refl _⟩

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- For an isomorphism of schemes `e : X ≅ Y`, the derived lower shriek `Re_!` is a left
adjoint, for any coefficient category: `Re_! ≅ Re_* ≅ L(e⁻¹)^*`, and `L(e⁻¹)^*` is left adjoint to
`R(e⁻¹)_*`. -/
instance isLeftAdjoint_rightDerivedLowerShriek_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (R(e.hom)_![A]).IsLeftAdjoint :=
  have := (derivedUpperStarLowerStarAdjunction A e.inv).isLeftAdjoint
  Functor.isLeftAdjoint_of_iso
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A e.hom ≪≫
      rightDerivedLowerStarIsoLeftDerivedUpperStarInv A e).symm

/-- For an isomorphism of schemes `e : X ≅ Y`, the exceptional inverse image along `e` is the
derived pullback, `Re^! ≅ Le^*`: both are right adjoint to `Re_! ≅ Re_* ≅ L(e⁻¹)^*`. -/
noncomputable def rightDerivedUpperShriekIsoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    R(e.hom)^![A] ≅ L((e.hom)^*[A]) :=
  ((rightDerivedUpperShriekAdjunction A e.hom).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar A e.hom ≪≫
        rightDerivedLowerStarIsoLeftDerivedUpperStarInv A e)).rightAdjointUniq
    ((derivedUpperStarLowerStarAdjunction A e.inv).ofNatIsoRight
      (rightDerivedLowerStarIsoLeftDerivedUpperStarInv A e.symm))

end Etale

end AlgebraicGeometry
