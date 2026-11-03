/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientPairingChange.GeneralEtalePairingChangeMaps

/-! # Ordinary fixed-coefficient projection comparison

Source: thm-coef-finite-hom, paragraph 4, projection part.
(blueprint: lem-coef-general-etale-direct-projection-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.GeneralCoefficientPairingChange
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
variable {S Z X : Scheme.{u}}

/-- Scalar change commutes with the direct-image projection on ordinary derived modules.
Source: Stacks 07A4 and 0GL6; thm-coef-finite-hom, paragraph 4.
(blueprint: lem-coef-general-etale-direct-projection-change).

Proof. The directImageMaps.etale_counit scalar-unit equation fixes the geometric
mate scalarPullComparison. Resolve both arguments by flat-term K-flat complexes.
The fixed scalar tensor comparison is the unique ordinary balancing comparison.
The pullback/scalar comparison is obtained by pulling back the scalar unit and
transposing it; on these representatives it is ordinary pullback of scalar
balancing. Both orders in the binary pullback/scalar tensor square send a pure
tensor to the same scalar-balanced tensor, and respect the total differential.
Descend that square along the K-flat resolutions. Apply the B-geometric
adjunction to both sides of the asserted projection equation. The mate-counit
identity, tensor naturality and the binary square identify the transposes.
Injectivity of the adjunction hom equivalence proves the equation. This argument
uses only ordinary coefficients, with no boundedness or flatness of B over A.
-/
theorem directProjection_change (φ : A →+* B) (g : Z ⟶ X)
    (K : DerivedCategoryModule A Z) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat B) X).map ((directImageMaps.etale φ g).app K)).app
        ((scalarExtension φ X).obj T) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).app
        ((scalarExtension φ Z).obj K)).app ((scalarExtension φ X).obj T) ≫
      R(lowerStar (ModuleCat B) g).map
        (((derivedTensor (ModuleCat B) Z).obj ((scalarExtension φ Z).obj K)).map
            ((scalarPullComparison φ g).app T) ≫
          (tensorComparison Z φ K (L(upperStar (ModuleCat A) g).obj T)).hom) =
    (tensorComparison X φ (R(lowerStar (ModuleCat A) g).obj K) T).hom ≫
      (scalarExtension φ X).map
        (((rightDerivedLowerStarProjectionMap (ModuleCat A) g).app K).app T) ≫
      (directImageMaps.etale φ g).app
        (((derivedTensor (ModuleCat A) Z).obj K).obj
          (L(upperStar (ModuleCat A) g).obj T)) := by sorry

end AlgebraicGeometry.Etale.GeneralCoefficientPairingChange
