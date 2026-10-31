/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionConstantComplexPullback

/-!
# The identification `Ψ Λ_X ≅ Λ'_X` pulled back from a base

Let `Ψ` be the derived extension of scalars along a surjection `ρ : Λ →+* Λ'` with principal
kernel. For `t : X ⟶ S`, the identification `Ψ Λ_X ≅ Λ'_X` pulled back along `t` from the
counit `η : Ψ Λ_S ≅ Λ'_S` of the oplax monoidal `Ψ`
(`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIsoOfPullback`) is the counit
`η : Ψ Λ_X ≅ Λ'_X` (`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexEtaIso`), as soon
as the canonical maps `Λ ⟶ Res Λ'` of the homotopy categories are compatible with `t^*`
(`AlgebraicGeometry.Etale.HomotopyUnitRestrictScalarsCompat`): both are determined by their
transposes under `Ψ ⊣ Res`, which agree by
`leftDerivedUpperStar_map_unit_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

/-- The counit `η : Ψ Λ ≅ Λ'` pulled back along `t : X ⟶ S` is the counit on `X`, provided the
canonical maps `Λ ⟶ Res Λ'` of the homotopy categories are compatible with `t^*`. -/
theorem derivedExtendScalarsConstantComplexIsoOfPullback_etaIso {X S : Scheme.{u}} (t : X ⟶ S)
    (H : HomotopyUnitRestrictScalarsCompat ρ t) :
    derivedExtendScalarsConstantComplexIsoOfPullback hρ ha
        (derivedExtendScalarsConstantComplexEtaIso hρ ha S) t =
      derivedExtendScalarsConstantComplexEtaIso hρ ha X := by
  ext
  apply derivedExtendScalars_hom_ext hρ ha
  have hb := leftDerivedUpperStar_map_unit_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom
    hρ ha t H
  have hn : (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app _ ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        ((L((t)^*[ModuleCat.{u + 1} Λ'])).map
          (derivedExtendScalarsConstantComplexEtaIso hρ ha S).hom) =
      (L((t)^*[ModuleCat.{u + 1} Λ])).map ((Sheaf.derivedRestrictScalars S.smallEtaleTopology ρ).map
        (derivedExtendScalarsConstantComplexEtaIso hρ ha S).hom) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app _ :=
    ((leftDerivedUpperStarRestrictScalarsIso ρ t).hom.naturality _).symm
  simp only [derivedExtendScalarsConstantComplexIsoOfPullback, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, derivedExtendScalarsPullbackIso_hom, Functor.map_comp]
  erw [(derivedExtendScalarsAdjunction hρ ha X).unit_naturality_assoc]
  rw [unit_app_comp_map_derivedExtendScalarsPullbackMap_app_assoc, reassoc_of% hn,
    ← Functor.map_comp_assoc, hb, Iso.inv_hom_id_assoc]

/-- **`Ψ Λ_X ≅ Λ'_X` pulled back from the terminal scheme is the counit `η`**, provided the
canonical maps `Λ ⟶ Res Λ'` of the homotopy categories are compatible with the pullback along
`X ⟶ ⊤_`. -/
theorem derivedExtendScalarsConstantComplexIso_eq_etaIso_of_compat (X : Scheme.{u})
    (H : HomotopyUnitRestrictScalarsCompat ρ (terminal.from X)) :
    derivedExtendScalarsConstantComplexIso hρ ha X =
      derivedExtendScalarsConstantComplexEtaIso hρ ha X :=
  derivedExtendScalarsConstantComplexIsoOfPullback_etaIso hρ ha _ H

end Etale

end AlgebraicGeometry
