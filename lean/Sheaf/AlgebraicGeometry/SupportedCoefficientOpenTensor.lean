/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientDerivedOpenMate

/-!
# Open pullback of the supported coefficient tensor comparison

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, steps 5 and 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

/-- Identify the derived first coefficient functor with coefficients followed by the
canonical derived projection inverse image.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstCoefficientProjectionIso (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] :
    (supportedFirstCoefficients A f g b).mapDerivedCategory ≅
      (supportedCoefficients A b).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor :=
  Functor.mapDerivedCategoryCompIso (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)) ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A b).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).symm

/-- The analogous comparison for the second projection.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportSecondCoefficientProjectionIso (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] :
    (supportedSecondCoefficients A f g d).mapDerivedCategory ≅
      (supportedCoefficients A d).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor :=
  Functor.mapDerivedCategoryCompIso (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)) ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A d).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).symm

/-- Pull the first supported coefficient to the open product, in the direction of the
mate of support restriction.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstOpenCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (U : X.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U)).mapDerivedCategory.obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.obj
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M) :=
  (supportFirstCoefficientProjectionIso A (U.ι ≫ f) g (supportOnOpen b U)).hom.app M ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g)).leftDerivedFunctor.map
      ((supportCoefficientOpenMate A U.ι b (supportOnOpen b U)
        (supportOnOpen_complement b U)).app M) ≫
    (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      (pullback.fst f g) (pullback.fst (U.ι ≫ f) g) U.ι
      (supportedFirstOpenMap_fst f g U)
      ((supportedCoefficients A b).mapDerivedCategory.obj M)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
      ((supportFirstCoefficientProjectionIso A f g b).inv.app M)

/-- Pull the uncut second supported coefficient to the open product.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstOpenSecondCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (U : X.Opens) (N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedSecondCoefficients A (U.ι ≫ f) g d).mapDerivedCategory.obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.obj
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N) :=
  (supportSecondCoefficientProjectionIso A (U.ι ≫ f) g d).hom.app N ≫
    (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
      (supportedFirstOpenMap_snd f g U)
      ((supportedCoefficients A d).mapDerivedCategory.obj N)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
      ((supportSecondCoefficientProjectionIso A f g d).inv.app N)

/-- The coefficient tensor comparison commutes with open pullback in the first variable.
This statement involves arbitrary coefficient complexes and no supported-section inputs
or evaluation maps.

Source: Stacks Project Tags 09XP and 0F1E, coefficient calculation in steps 5 and 11
of lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-open-tensor).
Proof: the left mates of the ordinary support restrictions are inverse images of the
closed supported constant coefficient functors, normalized by their quotient maps.
Cancel the quotient from the constant sheaf to check the ordinary tensor square: both
maps restrict and multiply the same two local constants. On each tensor bidegree this
is the same square for the signed total comparison. Localizing K-flat coefficient
complexes gives the displayed equality, by the normalization of the derived coefficient
tensor comparison. Naturality and the existence of K-flat models extend it to arbitrary
coefficient complexes. The normalized derived-adjunction units identify the left mates
of derived restrictions with the derived ordinary left mates. This includes empty opens
and empty supports, where the corresponding coefficient sheaves vanish. -/
theorem supportedCoefficientTensor_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportCoefficientOpenMate A (supportedFirstOpenMap f g U)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportedFirstOpenSupport_complement f g b d U)).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
        (supportedCoefficientTensorDerived A f g b d M N) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M)
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A (U.ι ≫ f) g (supportOnOpen b U) d M N ≫
      supportedDerivedTensorMap A (pullback (U.ι ≫ f) g)
        (supportFirstOpenCoefficientMap A f g b U M)
        (supportFirstOpenSecondCoefficientMap A f g d U N) := by
  sorry

end AlgebraicGeometry.Etale
