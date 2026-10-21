/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor

/-!
# Open pullback in the second coefficient

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, steps 5 and 11.
-/

@[expose] public section
set_option autoImplicit false
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Pull the uncut first supported coefficient to the second open product.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-second-open-tensor). -/
noncomputable def supportSecondOpenFirstCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (V : Y.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedFirstCoefficients A f (V.ι ≫ g) b).mapDerivedCategory.obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.obj
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M) :=
  (supportFirstCoefficientProjectionIso A f (V.ι ≫ g) b).hom.app M ≫
    (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
      (supportedSecondOpenMap_fst f g V)
      ((supportedCoefficients A b).mapDerivedCategory.obj M)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
      ((supportFirstCoefficientProjectionIso A f g b).inv.app M)

/-- Pull the second supported coefficient to the open product by the mate of restriction.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-second-open-tensor). -/
noncomputable def supportSecondOpenCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (V : Y.Opens) (N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V)).mapDerivedCategory.obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.obj
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N) :=
  (supportSecondCoefficientProjectionIso A f (V.ι ≫ g) (supportOnOpen d V)).hom.app N ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g))).leftDerivedFunctor.map
      ((supportCoefficientOpenMate A V.ι d (supportOnOpen d V)
        (supportOnOpen_complement d V)).app N) ≫
    (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      (pullback.snd f g) (pullback.snd f (V.ι ≫ g)) V.ι
      (supportedSecondOpenMap_snd f g V)
      ((supportedCoefficients A d).mapDerivedCategory.obj N)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
      ((supportSecondCoefficientProjectionIso A f g d).inv.app N)

/-- The coefficient tensor comparison commutes with open pullback in the second variable.
It is independent of supported-section inputs and evaluation maps.

Source: Stacks Tags 09XP and 0F1E, coefficient calculation in steps 5 and 11 of
lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-second-open-tensor).
Proof: normalize each ordinary coefficient comparison by its epic quotient from the
constant sheaf. The mates of support restriction carry this quotient to its pullback.
After precomposition with the constant quotient, both sides of the coefficient square
pull back and tensor the same local constants. Cancel the quotient. Apply this equality
in every bidegree of the signed total complex. The canonical tensor pullback comparison
has exactly this bidegree normalization. Descend along K-flat coefficient models using
the normalization of supportedCoefficientTensorDerived and derived-adjunction units.
Every derived coefficient object admits such a model, and naturality transports the
result along the model isomorphisms. Empty opens and supports give zero coefficient
sheaves, so the same calculation applies in those cases. -/
theorem supportedCoefficientTensor_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (V : Y.Opens)
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportCoefficientOpenMate A (supportedSecondOpenMap f g V)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
      (supportedSecondOpenSupport_complement f g b d V)).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
        (supportedCoefficientTensorDerived A f g b d M N) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M)
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A f (V.ι ≫ g) b (supportOnOpen d V) M N ≫
      supportedDerivedTensorMap A (pullback f (V.ι ≫ g))
        (supportSecondOpenFirstCoefficientMap A f g b V M)
        (supportSecondOpenCoefficientMap A f g d V N) := by
  sorry

end AlgebraicGeometry.Etale
