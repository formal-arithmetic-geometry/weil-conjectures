/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit

/-!
# Finite source coefficient models for rational Ext
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- A lisse source has a finite coefficient model with the specified coefficient map. -/
theorem rationalExt_finiteSourceModel
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) S))
    (hL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) L) :
    ∃ (E₀ : PadicAlgCl.FiniteIntermediateField ℓ)
      (f : Profinite.continuousMapRingSheaf.{u} E₀ ⟶ Λ),
      ((∃ h : Profinite.continuousMapRingSheaf.{u} E₀ = Λ, f = eqToHom h) ∨
        ∃ h : Profinite.padicAlgClCondensedRing.{u} ℓ = Λ,
          f = Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E₀ ≫ eqToHom h) ∧
      ∃ Lmodel : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E₀) S),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E₀) Lmodel ∧
      Nonempty ((Mod.extendScalars ((upperStarFromPoint S).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))).obj Lmodel ≅ L)  := by
  rcases hΛ with ⟨E, hE, rfl⟩ | rfl
  · let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨E, hE⟩
    refine ⟨E₀, 𝟙 _, Or.inl ⟨rfl, rfl⟩, L, hL, ?_⟩
    have hid : (upperStarFromPoint S).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (𝟙 (Profinite.continuousMapRingSheaf.{u} E₀))) = 𝟙 _ := by
      exact (congrArg ((upperStarFromPoint S).map)
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_id _)).trans
            ((upperStarFromPoint S).map_id _)
    exact ⟨(Mod.extendScalarsIsoOfEq hid).app L ≪≫ Mod.extendScalarsId.app L⟩
  · obtain ⟨E, Lmodel, hLm, he⟩ := (coefficient_finite_descent_lisse S ℓ).1 L hL
    refine ⟨E, Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E,
      Or.inr ⟨rfl, ?_⟩, Lmodel, hLm, he⟩
    simp

end AlgebraicGeometry.ProEtale
