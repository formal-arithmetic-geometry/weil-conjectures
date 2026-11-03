/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientPairingChange.GeneralEtalePairingChangeMaps

/-! # Ordinary fixed-coefficient projection comparison

Source: thm-coef-finite-hom, paragraph 4, projection part.
(blueprint: lem-coef-general-etale-open-projection-change).
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

/-- Scalar change commutes with inverse open projection on ordinary derived modules.
Source: Stacks 07A4 and 0GL6; thm-coef-finite-hom, paragraph 4.
(blueprint: lem-coef-general-etale-open-projection-change).

Proof. The fixed open scalar comparison is the unique composite-left-adjoint
isomorphism for the actual coefficient restrictions and exact open restrictions.
On flat-term K-flat models its map is extension by zero of ordinary scalar
balancing: a section supported in the open, tensored with b, maps to the same
supported section with coefficient b. The inverse open projection is the
transpose of the open adjunction unit tensored with restriction. Compare the two
routes on a local supported tensor generator. Both routes send it to the
extension by zero of the same tensor, with the same product of scalar
coefficients. The scalarPullComparison used here is the geometric mate of the
ordinary directImageMaps.etale; its scalar-unit equation etale_counit identifies
it on those models with that same scalar/restriction map. The signed total tensor
differentials coincide since the coefficients have degree zero. Exact extension
and restriction preserve these K-flat models. Descend the generator equality by
sheafification and localization, and use naturality along resolutions to obtain
the displayed equation on every derived input. The empty open and zero objects
obey the same unit equation; no nonemptiness or coefficient-flatness is needed.
-/
theorem openProjection_change (φ : A →+* B) (j : S ⟶ Z)
    [IsOpenImmersion j] (K : DerivedCategoryModule A S) (T : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat B) Z).map ((fixedOpenScalarExtension φ j).hom.app K)).app
        ((scalarExtension φ Z).obj T) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app
        ((scalarExtension φ S).obj K)).app ((scalarExtension φ Z).obj T) ≫
      (derivedExtension (A := B) j).map
        (((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
            ((scalarPullComparison φ j).app T) ≫
          (tensorComparison S φ K (L(upperStar (ModuleCat A) j).obj T)).hom) =
    (tensorComparison Z φ ((derivedExtension (A := A) j).obj K) T).hom ≫
      (scalarExtension φ Z).map
        (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app K).app T) ≫
      (fixedOpenScalarExtension φ j).hom.app
        (((derivedTensor (ModuleCat A) S).obj K).obj
          (L(upperStar (ModuleCat A) j).obj T)) := by sorry

end AlgebraicGeometry.Etale.GeneralCoefficientPairingChange
