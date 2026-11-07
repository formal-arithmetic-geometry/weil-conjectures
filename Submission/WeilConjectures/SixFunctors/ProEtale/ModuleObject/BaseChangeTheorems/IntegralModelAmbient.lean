/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Integral models in the ambient derived category

On a noetherian scheme `X`, every bounded constructible `ℚ̄_ℓ`-complex `K` is
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for a finite subextension `E` and a bounded constructible
`𝒪_E`-complex `K₀` (`ProEtale.exists_padicAlgCl_iso_integralModel`). This file restates this in the
ambient derived categories, with the properties of `K₀` used to lift split monomorphisms: `K₀` is
derived complete and bounded below
(`ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

set_option maxHeartbeats 1000000 in
-- the existential statement is matched against the large types of the coefficient changes
/-- **Integral models in the ambient derived category**: on a noetherian scheme, a bounded
constructible `ℚ̄_ℓ`-complex `K` is `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for a derived complete, bounded
constructible `𝒪_E`-complex `K₀`. -/
theorem exists_derivedCompleteIntegers_iso_integralModel (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K) :
    ∃ (E : FiniteIntermediateField ℓ) (K₀ : DerivedCategory (Mod
        (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ),
      derivedCompleteIntegers ℓ E X K₀ ∧ K₀.IsGE n ∧ boundedConstructible _ K₀ ∧
        Nonempty ((L(Mod.extendScalars (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))).obj
            ((L(Mod.extendScalars (coefficientMap
              (padicIntegersRingObjToContinuousMapRingObj ℓ E) X))).obj K₀) ≅ K) := by
  let K' : PadicAlgClConstructible X ℓ := ⟨K, by exact_mod_proofs hK⟩
  have H := exists_padicAlgCl_iso_integralModel X ℓ K'
  choose E K₀ he using H
  obtain ⟨e⟩ := he
  have hobj : (ObjectProperty.ι _).obj K' = K := rfl
  have i₁ := (ObjectProperty.liftCompιIso (boundedConstructible (padicAlgClRingObj X ℓ))
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)).app
      ((boundedConstructibleExtendScalars X ℓ E).obj K₀)
  have i₂ := (derivedExtendScalarsToPadicAlgCl X ℓ E).mapIso
    ((boundedConstructibleExtendScalarsCompatibility X ℓ E).app K₀)
  have hK₀ : boundedConstructible _ K₀.obj := by exact_mod_proofs K₀.property
  obtain ⟨n, hn⟩ := hK₀.1.1
  have hc := derivedCompleteIntegers_of_boundedConstructible hK₀
  have hne := Nonempty.intro ((i₁ ≪≫ i₂).symm ≪≫ (ObjectProperty.ι _).mapIso e ≪≫ eqToIso hobj)
  refine ⟨E, K₀.obj, n, by exact_mod_proofs hc, hn, hK₀, ?_⟩
  exact hne

end AlgebraicGeometry.ProEtale.CondensedRing
