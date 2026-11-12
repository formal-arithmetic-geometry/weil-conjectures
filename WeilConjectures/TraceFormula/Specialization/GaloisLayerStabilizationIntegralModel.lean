/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationPadicAlgCl

/-!

# Stabilization of nearby cycles along the Galois layers at a given integral model

Let `N` be a model, `h : N.generic ⟶ Spec L` and `Ω/L` an extension. Let `C` be a
`ℚ̄_ℓ`-complex with an integral model of `Lε^* C`: a finite subextension `E ⊆ ℚ̄_ℓ`, a bounded
constructible `𝒪_E`-complex `K₀` on the noetherian generic fibre and an isomorphism
`ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ Lε^* C` (as produced by `ProEtale.exists_padicAlgCl_iso_integralModel`). If
the restricted base change morphism of `Rj_*` along the change of Galois layers `N_Ω ⟶ N_{L'}`
is invertible with `𝔽_E`-coefficients at the reduction of `K₀`, then the pullback exchange of
`N_Ω ⟶ N_{L'}` is invertible at `C`
(`NearbyCyclesModel.isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_integralModel`).

This is the argument of
`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl`, whose hypothesis
is quantified over all integral models, at the given integral model: derived Nakayama from
`𝔽_E` to `𝒪_E`, then flat extension of scalars from `𝒪_E` to `E` to `ℚ̄_ℓ`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] (ℓ : ℕ) [Fact ℓ.Prime]

set_option profiler true in
/-- **Nearby cycles stabilize at a finite Galois layer, `ℚ̄_ℓ`-coefficients, at a given integral
model.** Let `C` be a `ℚ̄_ℓ`-complex and `K₀` a bounded constructible `𝒪_E`-complex on the
noetherian generic fibre with `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ Lε^* C`. If there is a finite Galois
subextension `L'` of `Ω/L` such that the base change morphism of `Rj_*` along `N_Ω ⟶ N_{L'}`,
restricted to the special fibre, is invertible with `𝔽_E`-coefficients at the reduction
`𝔽_E ⊗ᴸ Lg^* K₀`, then the pullback exchange of `N_Ω ⟶ N_{L'}` is invertible at `C`.

This is the argument of
`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl` at the given
integral model. -/
theorem isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_integralModel
    [IsNoetherian N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [QuasiCompact N.j] [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))
    (e : (constructibleToPadicAlgCl N.generic ℓ E).obj
      ((boundedConstructibleExtendScalars N.generic ℓ E).obj K₀) ≅ ⟨_, hC⟩)
    (L' : FiniteGaloisIntermediateField L Ω)
    (hL' : IsIso ((L(((N.galoisLayer h Ω).i)^*⟦Profinite.continuousMapRingObj.{u}
            (integersResidueField ℓ E.1)⟧)).map
          ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayer h L'.toIntermediateField).j)
            (derivedUpperStarLowerStarAdjunction
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayer h Ω).j)
            (pullbackSquareComparison
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayerRestrict h Ω L'.toIntermediateField).commSq_j)).app
            ((Mod.extendScalars (coefficientMap
              (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                (N.galoisLayer h L'.toIntermediateField).generic)).leftDerivedFunctor.obj
              ((L(upperStar (Profinite.padicIntegersRingObj ℓ E.1)
                (N.galoisLayerHom h L'.toIntermediateField).generic)).obj K₀.obj))))) :
    IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app C) := by
  have hK₀ : boundedConstructible _ K₀.obj := by exact_mod_proofs K₀.property
  -- the hypotheses carry different proofs of `Precoherent Profinite`, which are identified
  revert C hC E K₀ e hL' hK₀
  normalize_precoherent
  intro C hC E K₀ e hL' hK₀
  -- finiteness properties of the Galois layers
  have i₁ := N.compactSpace_galoisLayer_generic h L'.toIntermediateField
  have i₂ := N.quasiSeparatedSpace_galoisLayer_generic h L'.toIntermediateField
  have i₃ := N.compactSpace_galoisLayer_generic h Ω
  have i₄ := N.quasiSeparatedSpace_galoisLayer_generic h Ω
  have i₅ := N.quasiCompact_galoisLayer_j h L'.toIntermediateField
  have i₆ := N.quasiSeparated_galoisLayer_j h L'.toIntermediateField
  have i₇ := N.quasiCompact_galoisLayer_j h Ω
  have i₈ := N.quasiSeparated_galoisLayer_j h Ω
  have i₉ : CompactSpace (N.galoisLayer h L'.toIntermediateField).total :=
    inferInstanceAs (CompactSpace N.total)
  have i₁₀ : QuasiSeparatedSpace (N.galoisLayer h L'.toIntermediateField).total :=
    inferInstanceAs (QuasiSeparatedSpace N.total)
  have i₁₁ : CompactSpace (N.galoisLayer h Ω).total := inferInstanceAs (CompactSpace N.total)
  have i₁₂ : QuasiSeparatedSpace (N.galoisLayer h Ω).total :=
    inferInstanceAs (QuasiSeparatedSpace N.total)
  -- from `𝔽_E` to `ℚ̄_ℓ` at the pullback `Lg^* K₀` of the integral model
  obtain ⟨n, hn⟩ := hK₀.1.1
  have hgn := isGE_leftDerivedUpperStar_obj _ (N.galoisLayerHom h L'.toIntermediateField).generic
    K₀.obj n
  have hc := derivedCompleteIntegers_leftDerivedUpperStar_obj
    (N.galoisLayerHom h L'.toIntermediateField).generic
    (derivedCompleteIntegers_of_boundedConstructible hK₀)
  have h₃ := isIso_map_baseChangeMap_app_padicAlgCl_of_residueField ℓ E
    (N.galoisLayerRestrict h Ω L'.toIntermediateField).commSq_j (N.galoisLayer h Ω).i _ n hc
    (by exact_mod_proofs hL')
  -- the integral model as an object of the ambient derived category, `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ Lε^* C`
  have e' := Nonempty.intro ((ObjectProperty.ι _).mapIso e)
  have hgen := isIso_map_baseChangeMap_app_leftDerivedUpperStar_of_iso_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    (N.galoisLayerRestrict h Ω L'.toIntermediateField).commSq_j (N.galoisLayer h Ω).i
    (N.galoisLayerHom h L'.toIntermediateField).generic K₀.obj
    (K := L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)
  -- reduction to the restricted base change map at `Lg^* (Lε^* C)`
  refine Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app _ _ C ?_
  refine isIso_map_app_of_iso _ _ (A := L(upperStar (Profinite.padicAlgClRingObj ℓ)
      (N.galoisLayerHom h L'.toIntermediateField).generic).obj
        (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) ((leftDerivedUpperStarComp _
    (N.galoisLayerHom h L'.toIntermediateField).generic N.ε).app C).symm ?_
  -- the hypotheses carry different proofs of `Precoherent Profinite`, which are identified
  clear e hK₀ hL' hc hgn hC i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉ i₁₀ i₁₁ i₁₂
  revert C E K₀ L' n hn h₃ e' hgen
  normalize_precoherent
  intro L' _ C E K₀ n hn h₃ e' hgen
  exact hgen e' h₃

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
