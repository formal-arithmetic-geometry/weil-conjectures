/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama

/-!
# The étale reduction modulo `ℓⁿ` reflects isomorphisms

For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `n ≠ 0`, a morphism `φ` of bounded constructible
`𝒪_E`-complexes on a separated `k`-scheme of finite type is an isomorphism as soon as its
reduction modulo `ℓⁿ` read on the small étale site
(`AlgebraicGeometry.ProEtale.CondensedRing.etaleReduction`) is one
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_of_isIso_etaleReduction_map`). This is the form
of derived Nakayama used to check isomorphisms of `ℓ`-adic complexes at finite level, for
instance the base change of the smooth orientation.

## Proof

The étale reading of `𝒪_E ⧸ ℓⁿ`-complexes is fully faithful
(`ProEtale.CondensedRing.finiteEtaleReadingFullyFaithful`, the reading of a bounded
constructible complex being of étale origin), so the reduction `φ ⊗ᴸ 𝒪_E ⧸ ℓⁿ` is an
isomorphism. The cone `C` of `φ` is bounded constructible and its reduction vanishes; the
reduction triangle `C --ℓⁿ--> C ⟶ C ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶` shows that `ℓⁿ` acts invertibly on `C`, so
`C = 0` by derived Nakayama (`ProEtale.isZero_of_isIso_pow_zsmul_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {n : ℕ}

/-- A morphism of bounded constructible `𝒪_E`-complexes whose reduction modulo `ℓⁿ` is an
isomorphism is an isomorphism, provided bounded constructible complexes on which `ℓⁿ` acts
invertibly vanish (derived Nakayama, `ProEtale.isZero_of_isIso_pow_zsmul_id`): `ℓⁿ` acts
invertibly on the cone, by the reduction triangle. -/
theorem isIso_of_isIso_boundedConstructibleIntegersModPowReduction_map (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (hZ : ∀ C : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X),
      IsIso (((ℓ : ℤ) ^ n) • 𝟙 C.obj) → IsZero C)
    {K L : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (φ : K ⟶ L) (h : IsIso ((boundedConstructibleIntegersModPowReduction X ℓ E n).map φ)) :
    IsIso φ := by
  have h₂ : IsIso ((L(Mod.extendScalars (integersModPowReduction X ℓ E n))).map
      ((boundedConstructible _).ι.map φ)) :=
    (NatIso.isIso_map_iff
      (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n) φ).1
      (inferInstanceAs (IsIso ((boundedConstructible _).ι.map
        ((boundedConstructibleIntegersModPowReduction X ℓ E n).map φ))))
  have := isTriangulated_boundedConstructible_padicIntegersRingObj X ℓ E
  suffices IsIso ((boundedConstructible _).ι.map φ) from
    isIso_of_reflects_iso φ (boundedConstructible _).ι
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle ((boundedConstructible _).ι.map φ)
  have hC : boundedConstructible _ C :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT K.property L.property
  have hF := (L(Mod.extendScalars (integersModPowReduction X ℓ E n))).map_distinguished _ hT
  have hz : IsZero ((L(Mod.extendScalars (integersModPowReduction X ℓ E n))).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ hF).2 h₂
  obtain ⟨g', h', hT'⟩ := exists_distinguished_integersModPowReduction X ℓ E n C
  have hz' : IsZero ((D(Mod.comap (integersModPowReduction X ℓ E n))).obj
      ((L(Mod.extendScalars (integersModPowReduction X ℓ E n))).obj C)) :=
    Functor.map_isZero _ hz
  have hiso : IsIso (((ℓ : ℤ) ^ n) • 𝟙 C) := (Triangle.isZero₃_iff_isIso₁ _ hT').1 hz'
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (((boundedConstructible _).ι).map_isZero (hZ ⟨C, hC⟩ hiso))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {n : ℕ}
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The étale reduction modulo `ℓⁿ` reflects isomorphisms**, `n ≠ 0`: a morphism of bounded
constructible `𝒪_E`-complexes whose reduction modulo `ℓⁿ`, read on the small étale site, is an
isomorphism is an isomorphism (`lemma-reduction-derived-nakayama`). The Nakayama step is derived
completeness: a bounded constructible complex is derived `ℓ`-complete
(`derivedCompleteIntegers_of_boundedConstructible`,
`proposition-integral-constructibility-criterion`), and a derived complete complex whose reduction
vanishes is zero
(`isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction`). -/
theorem isIso_of_isIso_etaleReduction_map (hn : n ≠ 0)
    {K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧} (φ : K ⟶ L)
    (h : IsIso ((etaleReduction ℓ E n X).map φ)) : IsIso φ := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have h' : IsIso ((finiteEtaleReading ℓ E n X).map
      ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).map φ)) := h
  have h₁ : IsIso ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).map φ) :=
    (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X)).isIso_of_isIso_map _
  refine isIso_of_isIso_boundedConstructibleIntegersModPowReduction_map ℓ E X.left
    (fun C hC ↦ ?_) φ h₁
  -- the reduction of `C` vanishes: `ℓⁿ` kills the residue-field coefficients and acts invertibly
  have hC₁ : IsZero ((derivedReduction X.left ℓ E).obj C.obj) := by
    refine DerivedCategory.isZero_of_isIso_zsmul_id
      (Sheaf.zsmul_id_eq_zero_of_intCast_eq_zero ?_) (m := (ℓ : ℤ) ^ n) ?_
    · rw [Int.cast_pow, Int.cast_natCast, natCast_eq_zero_residueFieldCoeff, zero_pow hn]
    · have : (derivedReduction X.left ℓ E).Additive := inferInstanceAs (Functor.Additive (_ ⋙ _))
      rw [← (derivedReduction X.left ℓ E).map_id, ← Functor.map_zsmul]
      infer_instance
  -- hence `C` vanishes, being derived complete
  have hC₂ : IsZero C.obj :=
    isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction (ℓ := ℓ) (E := E)
      (derivedCompleteIntegers_of_boundedConstructible (ℓ := ℓ) (E := E) C.property) hC₁
  have : IsIso ((boundedConstructible _).ι.map (0 : C ⟶ C)) := by
    rw [Functor.map_zero]
    exact hC₂.isIso hC₂ _
  have : IsIso (0 : C ⟶ C) := (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _
  exact IsZero.of_mono_zero C C

end AlgebraicGeometry.ProEtale.CondensedRing
