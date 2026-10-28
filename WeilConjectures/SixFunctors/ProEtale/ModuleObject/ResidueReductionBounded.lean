/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.NumberTheory.Padics.IntegersModPowResidueField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueShortExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralRegularEnd

/-!
# The derived reduction to the residue field preserves boundedness

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and `X` a scheme. For a generator `ϖ` of the maximal ideal of `𝒪_E`, the sequence
`0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0` is short exact, so that the derived reduction
`K ↦ K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` sits in a triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` and preserves
bounded complexes (`ProEtale.bounded_derivedExtendScalars_padicIntegersToResidueField`). For
`n ≥ 1` the residue map factors through `𝒪_E ⧸ ℓⁿ`, so that the reduction to `𝔽_E` of the
reduction `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` modulo `ℓⁿ` of a bounded complex `K` is bounded
(`ProEtale.bounded_derivedExtendScalars_integersModPowToResidueField`).

These are the statements of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueShortExact` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible`, for a subfield `E`
given by an arbitrary `ℚ_ℓ`-algebra embedded in `ℚ̄_ℓ` rather than an intermediate field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- For `n ≥ 1`, the residue map `𝒪̲_E ⟶ 𝔽̲_E` factors through the reduction
`𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`. -/
lemma padicIntegersRingObjToIntegersModPow_comp_continuousMapRingObjMap (n : ℕ) [NeZero n] :
    padicIntegersRingObjToIntegersModPow.{u} ℓ E n ≫
        continuousMapRingObjMap (PadicAlgCl.integersModPowToResidueField ℓ E n)
          continuous_of_discreteTopology =
      padicIntegersRingObjToResidueField ℓ E := by
  rw [padicIntegersRingObjToIntegersModPow, continuousMapRingObjMap, ← Functor.map_comp]
  rfl

/-- An element of the maximal ideal vanishes in `𝔽_E`: the multiplication by `ϖ ∈ 𝔪_E` on `𝒪̲_E`
followed by the residue map is zero. -/
lemma continuousMapRingObjMulLeft_comp_padicIntegersRingObjToResidueField
    (ϖ : PadicAlgCl.integers ℓ E) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E)) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    continuousMapRingObjMulLeft.{u} (PadicAlgCl.integers ℓ E) ϖ ≫
      padicIntegersRingObjToResidueField ℓ E = 0 := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have h0 : PadicAlgCl.integersResidue ℓ E ϖ = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hϖ
  ext S a
  refine ULift.ext _ _ (ContinuousMap.ext fun s ↦ ?_)
  refine (map_mul (PadicAlgCl.integersResidue ℓ E) ϖ (a.down s)).trans ?_
  rw [h0, zero_mul]
  rfl

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`0 ⟶ 𝒪̲_E --ϖ--> 𝒪̲_E ⟶ 𝔽̲_E ⟶ 0` is short exact** for a generator `ϖ` of the maximal ideal of
`𝒪_E`, checked on sections over each profinite set `S`. -/
lemma shortExact_continuousMapRingObjMulLeft_padicIntegersRingObjToResidueField
    (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    (ShortComplex.mk _ _
      (continuousMapRingObjMulLeft_comp_padicIntegersRingObjToResidueField.{u} ℓ E ϖ
        (hϖ ▸ Ideal.mem_span_singleton_self ϖ))).ShortExact := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let T := ShortComplex.mk _ _
    (continuousMapRingObjMulLeft_comp_padicIntegersRingObjToResidueField.{u} ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))
  have hne : ϖ ≠ 0 := fun h ↦ PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E (by
    rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hne' : (ϖ : E) ≠ 0 := fun h ↦ hne (Subtype.ext h)
  have hf (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)) (s) :
      (T.f.hom.app S a).down s = ϖ * a.down s := rfl
  have hg (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)) (s) :
      (T.g.hom.app S a).down s = PadicAlgCl.integersResidue ℓ E (a.down s) := rfl
  have hpre : (T.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun S ↦ ?_
    have h : ((T.map (sheafToPresheaf _ _)).map ((evaluation _ _).obj S)).Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro a ha
      have hz (s : S.unop) : a.down s ∈ Ideal.span {ϖ} := by
        rw [← hϖ, ← IsLocalRing.residue_eq_zero_iff]
        exact (hg S a s).symm.trans (congrArg (fun z : ULift.{u + 1} C(S.unop,
          PadicAlgCl.integersResidueField ℓ E) ↦ z.down s) ha)
      choose b hb using fun s ↦ Ideal.mem_span_singleton'.1 (hz s)
      have hbv (s : S.unop) : (b s : E) = (ϖ : E)⁻¹ * (a.down s : E) := by
        rw [← hb s, Subring.coe_mul, mul_comm (b s : E)]
        exact (inv_mul_cancel_left₀ hne' _).symm
      have hbc : Continuous b := by
        refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
        simp only [Function.comp_def, hbv]
        exact continuous_const.mul (continuous_subtype_val.comp a.down.continuous)
      exact ⟨ULift.up ⟨b, hbc⟩, ULift.ext _ _ (ContinuousMap.ext fun s ↦
        (hf S _ s).trans ((mul_comm _ _).trans (hb s)))⟩
    rw [ShortComplex.exact_iff_isZero_homology] at h
    exact h.of_iso ((T.map (sheafToPresheaf _ _)).mapHomologyIso ((evaluation _ _).obj S)).symm
  have hmono (S : Profinite.{u}ᵒᵖ) : Mono (((sheafToPresheaf _ _).map T.f).app S) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have h := congrArg ULift.down hab
    exact ULift.ext _ _ (ContinuousMap.ext fun s ↦ mul_left_cancel₀ hne
      (((hf S a s).symm.trans (congrArg (fun z : C(S.unop, PadicAlgCl.integers ℓ E) ↦ z s)
        h)).trans (hf S b s)))
  have hepi (S : Profinite.{u}ᵒᵖ) : Epi (((sheafToPresheaf _ _).map T.g).app S) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro c
    refine ⟨ULift.up ⟨Function.surjInv (PadicAlgCl.integersResidue_surjective ℓ E) ∘ c.down,
      continuous_of_discreteTopology.comp c.down.continuous⟩,
      ULift.ext _ _ (ContinuousMap.ext fun s ↦ ?_)⟩
    exact (hg S _ s).trans (Function.surjInv_eq _ _)
  have : Mono T.f := (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  have : Epi T.g := (sheafToPresheaf _ _).epi_of_epi_map (NatTrans.epi_of_epi_app _)
  refine ⟨?_⟩
  exact (ShortComplex.exact_iff_of_iso
    (T.mapNatIso (asIso (sheafificationAdjunction _ _).counit))).1
    (hpre.map (presheafToSheaf _ _))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
/-- The underlying map of `padicIntegersRegularEndOfAlgebra X ℓ E ϖ` is the image under `p_X^*`
of the multiplication by `ϖ` on `𝒪̲_E`. -/
lemma padicIntegersRegularEndOfAlgebra_hom (ϖ : PadicAlgCl.integers ℓ E) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom =
      (upperStarFromPoint X).map
        (Profinite.continuousMapRingObjMulLeft.{u} (PadicAlgCl.integers ℓ E) ϖ) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [← Mod.regularEndSMul_unit (padicIntegersRegularEndOfAlgebra X ℓ E ϖ),
    padicIntegersRegularEndOfAlgebra, Mod.regularEndSMul_regularLift_hom]
  erw [Mod.globalSmul_regular_obj (upperStarFromPoint X)]
  rw [Profinite.globalSmul_continuousMapConstRingHom]

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0` is short exact**, for a generator `ϖ` of the
maximal ideal, with `ϖ` seen as an endomorphism of the regular `𝒪_{E,X}`-module: the inverse
image along the exact functor `p_X^*` of the short exact sequence of condensed abelian groups
`Profinite.shortExact_continuousMapRingObjMulLeft_padicIntegersRingObjToResidueField`. -/
lemma shortExact_padicIntegersRegularEndOfAlgebra (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    (ShortComplex.mk (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom
      (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E) X) (by
        rw [padicIntegersRegularEndOfAlgebra_hom, ← Functor.map_comp,
          Profinite.continuousMapRingObjMulLeft_comp_padicIntegersRingObjToResidueField ℓ E ϖ
            (hϖ ▸ Ideal.mem_span_singleton_self ϖ), Functor.map_zero])).ShortExact := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  refine ShortComplex.shortExact_of_iso ?_
    ((Profinite.shortExact_continuousMapRingObjMulLeft_padicIntegersRingObjToResidueField.{u}
      ℓ E ϖ hϖ).map_of_exact (upperStarFromPoint X))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [padicIntegersRegularEndOfAlgebra_hom]) (by simp)

/-- **The derived reduction to the residue field preserves boundedness**: if
`K ∈ D(Mod_{𝒪_{E,X}})` is bounded, so is `K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}`. By the reduction triangle
`K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` for a uniformizer `ϖ`, its restriction of scalars to `𝒪_{E,X}` is
bounded, and restriction of scalars is exact and faithful. -/
theorem bounded_derivedExtendScalars_padicIntegersToResidueField
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.TStructure.t.bounded
      ((Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E)
        X)).leftDerivedFunctor.obj K) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨_, _, _, hT⟩ := Mod.exists_distinguished_regularEndSMul_derivedExtendScalars _
    (shortExact_padicIntegersRegularEndOfAlgebra X ℓ E ϖ hϖ) K
  let φ := coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E) X
  have h₃ : DerivedCategory.TStructure.t.bounded
      ((Mod.comap φ).mapDerivedCategory.obj ((Mod.extendScalars φ).leftDerivedFunctor.obj K)) :=
    DerivedCategory.TStructure.t.bounded.ext_of_isTriangulatedClosed₃ _ hT hK hK
  rw [← DerivedCategory.exists_homologyConcentratedIn_iff_bounded] at h₃ ⊢
  obtain ⟨a, b, hab⟩ := h₃
  exact ⟨a, b,
    (Mod.comap φ).homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj hab⟩

/-- For `n ≥ 1`, the reduction to the residue field `𝔽_E` of the reduction `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` of a
bounded complex `K ∈ D(Mod_{𝒪_{E,X}})` is bounded: it is `K ⊗ᴸ 𝔽_E`
(`CategoryTheory.Mod.derivedExtendScalarsCompIso`). -/
theorem bounded_derivedExtendScalars_integersModPowToResidueField (n : ℕ) [NeZero n]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.TStructure.t.bounded
      ((Mod.extendScalars (coefficientMap (Profinite.continuousMapRingObjMap.{u}
        (PadicAlgCl.integersModPowToResidueField ℓ E n) continuous_of_discreteTopology)
          X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K)) := by
  refine DerivedCategory.TStructure.t.bounded.prop_of_iso
    ((Mod.derivedExtendScalarsCompIso _ _ _ ?_).app K)
    (bounded_derivedExtendScalars_padicIntegersToResidueField X ℓ E K hK)
  rw [← Functor.map_comp,
    Profinite.padicIntegersRingObjToIntegersModPow_comp_continuousMapRingObjMap]

end AlgebraicGeometry.ProEtale
