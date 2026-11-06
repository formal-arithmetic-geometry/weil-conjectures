/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.Basic
public import Mathlib.Util.CountHeartbeats

/-!
# Coefficient change for restricted base change maps: from `E` to `ℚ̄_ℓ`

The invertibility of the restricted base change map
`Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K` passes from `E` to `ℚ̄_ℓ` by flat
extension of scalars
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

#count_heartbeats in
set_option maxHeartbeats 400000 in
-- The normalized proof exceeded 200000 heartbeats in the real-tree baseline (282s).
/-- **From `E` to `ℚ̄_ℓ` for the restricted base change map**: for quasi-compact quasi-separated
vertical maps, if the restricted base change map with `E`-coefficients is invertible at a
bounded below `K`, then the one with `ℚ̄_ℓ`-coefficients is invertible at `ℚ̄_ℓ ⊗ᴸ_E K`. -/
theorem isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) (n : ℤ) (hn : K.IsGE n)
    (h : IsIso ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
      (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app K))) :
    IsIso ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj K))) := by
  #count_heartbeats (have :=
    isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj E.1) g' K n)
  #count_heartbeats (have hA := isIso_map_baseChangeMap_app_derivedExtendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (derivedPullIsoCompCoherence _) sq i K
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p'
      ((g')^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj K) n))
  -- Align the proofs of `Precoherent Profinite` before applying the coefficient-change theorem.
  #count_heartbeats (revert h hA)
  #count_heartbeats normalize_precoherent
  #count_heartbeats (intro h hA)
  #count_heartbeats exact hA h

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
