/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerBoundaryRestrictScalars

/-!
# The restriction of scalars of the Kummer boundary

The restriction of scalars of the Kummer boundary with coefficients `Λ'` is the boundary of the
restricted Kummer sequence
(`AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso_hom_comp_map_kummerδ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}
  [HasInvertibleExponent Λ' X]

/-- The restriction of scalars of the Kummer boundary with coefficients `Λ'` is the boundary of
the restricted sequence, through `AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso`. -/
lemma singleFunctorRestrictScalarsIso_hom_comp_map_kummerδ
    {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    (singleFunctorRestrictScalarsIso ρ X C).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (kummerδ Λ' φ hC) ≫
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).commShiftIso
            (1 : ℤ)).hom.app _ =
      kummerδRestrictScalars ρ φ hC ≫
        ((singleFunctorRestrictScalarsIso ρ X (X.rootsOfUnitySheaf (ringChar Λ'))).hom)⟦(1 : ℤ)⟧' :=
  Sheaf.derivedRestrictScalars_map_singleδ_of_heq _ ρ
    (shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC)
    (Z₁ := (extendScalars Λ' X).obj (X.rootsOfUnitySheaf (ringChar Λ')))
    (Z₃ := (extendScalars Λ' X).obj C)
    (Y₁ := (extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
      (X.rootsOfUnitySheaf (ringChar Λ')))
    (Y₃ := (extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ).obj C)
    rfl rfl rfl rfl (singleFunctorRestrictScalarsIso ρ X _) HEq.rfl
    (singleFunctorRestrictScalarsIso ρ X _) HEq.rfl (kummerδ Λ' φ hC) HEq.rfl
    (kummerδRestrictScalars ρ φ hC) HEq.rfl

end AlgebraicGeometry.Etale
