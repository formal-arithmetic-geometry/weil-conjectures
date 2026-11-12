/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeAmbient
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers

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

private theorem exists_padicAlgCl_iso_integralModel_obj_aux (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : boundedConstructible _ K) :
    ∃ (E : FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)),
      Nonempty ((L(Mod.extendScalars (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))).obj
            ((L(Mod.extendScalars (coefficientMap
              (padicIntegersRingObjToContinuousMapRingObj ℓ E) X))).obj K₀.obj) ≅ K) := by
  exact exists_padicAlgCl_iso_integralModel_obj ℓ X K hK

private theorem derivedCompleteIntegers_boundedConstructible_aux (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} [IsNoetherian X] {E : FiniteIntermediateField ℓ}
    {K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)} :
    derivedCompleteIntegers ℓ E X K₀.obj :=
  derivedCompleteIntegers_of_boundedConstructible K₀.property

private theorem exists_isGE_boundedConstructible_aux (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {E : FiniteIntermediateField ℓ}
    {K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)} :
    ∃ n : ℤ, K₀.obj.IsGE n :=
  K₀.property.1.1

private theorem integralModel_obj_to_derivedComplete_aux (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} [IsNoetherian X] {E : FiniteIntermediateField ℓ}
    {K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)}
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (he : Nonempty ((L(Mod.extendScalars (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))).obj
            ((L(Mod.extendScalars (coefficientMap
              (padicIntegersRingObjToContinuousMapRingObj ℓ E) X))).obj K₀.obj) ≅ K)) :
    ∃ (n : ℤ), derivedCompleteIntegers ℓ E X K₀.obj ∧ K₀.obj.IsGE n ∧
      boundedConstructible _ K₀.obj ∧
        Nonempty ((L(Mod.extendScalars (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))).obj
            ((L(Mod.extendScalars (coefficientMap
              (padicIntegersRingObjToContinuousMapRingObj ℓ E) X))).obj K₀.obj) ≅ K) := by
  obtain ⟨n, hn⟩ := exists_isGE_boundedConstructible_aux ℓ (X := X) (E := E) (K₀ := K₀)
  exact ⟨n, derivedCompleteIntegers_boundedConstructible_aux ℓ (X := X) (E := E) (K₀ := K₀),
    hn, K₀.property, he⟩

private theorem exists_derivedCompleteIntegers_iso_integralModel_aux (ℓ : ℕ) [Fact ℓ.Prime]
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
  obtain ⟨E, K₀, he⟩ := exists_padicAlgCl_iso_integralModel_obj_aux ℓ X K hK
  obtain ⟨n, hcomplete, hn, hK₀, he⟩ := integralModel_obj_to_derivedComplete_aux ℓ he
  exact ⟨E, K₀.obj, n, hcomplete, hn, hK₀, he⟩

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
  exact exists_derivedCompleteIntegers_iso_integralModel_aux ℓ hK

end AlgebraicGeometry.ProEtale.CondensedRing
