/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Normalization comparison objects on the isomorphism locus
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The normalization comparison objects agree on the isomorphism locus. -/
theorem normalization_comparison_on_iso_locus {X X' U U' : Scheme.{u}}
    (ν : X' ⟶ X) [IsFinite ν] (V : X.Opens) [IsIso (ν ∣_ V)]
    (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'} [IsOpenImmersion j']
    {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ) :
    Nonempty (((V.ι)^*[ModuleCat.{u + 1} Λ].obj
      ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))) ≅
      ((V.ι)^*[ModuleCat.{u + 1} Λ].obj ((ν)_*[ModuleCat.{u + 1} Λ].obj
        ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))))) := by
  let A := ModuleCat.{u + 1} Λ
  let F := (j)_!open[A].obj (Etale.constantModSheaf Λ U ℓ)
  let G := (j')_!open[A].obj (Etale.constantModSheaf Λ U' ℓ)
  let W := ν ⁻¹ᵁ V
  let r := ν ∣_ V
  have hV : IsPullback W.ι r ν V.ι := (isPullback_morphismRestrict ν V).flip
  have hbc := Etale.isIso_openImmersionLowerShriekBaseChangeMap A hj.flip
  let ec : (ν')^*[A].obj (Etale.constantModSheaf Λ U ℓ) ≅
      Etale.constantModSheaf Λ U' ℓ :=
    (Scheme.upperStarConstantSheafIso A ν').app
      (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ)))
  let e : (ν)^*[A].obj F ≅ G :=
    (asIso ((Etale.openImmersionLowerShriekBaseChangeMap A hj.flip.toCommSq).app
      (Etale.constantModSheaf Λ U ℓ))).symm ≪≫ (j')_!open[A].mapIso ec
  let er : (r)^*[A].obj ((V.ι)^*[A].obj F) ≅ (W.ι)^*[A].obj G :=
    (Etale.squareUpperStarIso A hV.toCommSq).app F ≪≫ (W.ι)^*[A].mapIso e
  have hf := Etale.isIso_baseChangeMap_flip_of_isPullback A hV.flip
  exact ⟨asIso ((Etale.upperStarLowerStarAdjunction A r).unit.app
    ((V.ι)^*[A].obj F)) ≪≫ (r)_*[A].mapIso er ≪≫
    (asIso ((Etale.baseChangeMap A hV.toCommSq).app G)).symm⟩
end AlgebraicGeometry
