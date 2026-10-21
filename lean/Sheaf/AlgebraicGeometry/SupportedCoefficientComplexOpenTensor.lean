/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientOrdinaryOpenTensor
public import Sheaf.AlgebraicGeometry.SupportedTensorComplexSquare

/-! # The first open coefficient tensor square on signed complexes -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace AlgebraicGeometry.Etale

/-- The actual support mate on the first open product, before derivation.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-complex-open-tensor). -/
noncomputable def supportFirstOrdinaryOpenProductCoefficientNatTrans
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens) :
    supportedCoefficients A
        (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d) ⟶
      supportedCoefficients A (supportedProductImmersion f g b d) ⋙
        upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U) :=
  supportCoefficientMate
    (supportedCoefficientAdjunction A (supportedProductImmersion f g b d))
    (supportedCoefficientAdjunction A
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (supportTransport A (supportedFirstOpenMap f g U)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportedFirstOpenSupport_complement f g b d U))

/-- The canonical ordinary first-open coefficient square commutes on signed total complexes.
Source: Stacks Tag 0F1E, the total-complex step of the supported restriction calculation.
(blueprint: lem-pur-supported-coefficient-complex-open-tensor).
Proof: use the proved ordinary first-open coefficient square on each pair of modules.
The factor maps are the components of the constructed natural transformations.
Apply the generic signed-totalization square theorem to these transformations and the
normalized coefficient tensor transformations. This gives exactly the displayed maps,
with the Koszul differential conventions already fixed by totalization. No boundedness,
flatness, or injectivity assumption on the two complexes is needed. -/
theorem supportedCoefficientTensor_complexOpenFirst
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    supportedTensorComplexSquareCondition
      (supportedCoefficients A (supportedProductImmersion f g b d))
      (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
      (supportedCoefficients A
        (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
      (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U))
      (supportedSecondCoefficients A (U.ι ≫ f) g d)
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
      (supportedCoefficientTensorNatTrans A f g b d)
      (supportedCoefficientTensorNatTrans A (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportFirstOrdinaryOpenProductCoefficientNatTrans A f g b d U)
      (supportFirstOrdinaryOpenCoefficientNatTrans A f g b U)
      (supportFirstOrdinaryOpenSecondCoefficientNatTrans A f g d U) P Q := by
  exact supportedTensorComplex_square
    (supportedCoefficients A (supportedProductImmersion f g b d))
    (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
    (supportedCoefficients A
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
    (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U))
    (supportedSecondCoefficients A (U.ι ≫ f) g d)
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (supportedCoefficientTensorNatTrans A f g b d)
    (supportedCoefficientTensorNatTrans A (U.ι ≫ f) g (supportOnOpen b U) d)
    (supportFirstOrdinaryOpenProductCoefficientNatTrans A f g b d U)
    (supportFirstOrdinaryOpenCoefficientNatTrans A f g b U)
    (supportFirstOrdinaryOpenSecondCoefficientNatTrans A f g d U)
    (fun M N ↦ supportedCoefficientTensor_ordinaryOpenFirst A f g b d U M N) P Q

end AlgebraicGeometry.Etale
