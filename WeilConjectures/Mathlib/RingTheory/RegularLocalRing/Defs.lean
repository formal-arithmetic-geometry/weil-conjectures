/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Cutting a regular local ring down by part of a regular system of parameters

If `A` is a regular local ring and `f₁, …, f_c ∈ 𝔪` have linearly independent classes in the
cotangent space `𝔪 ⧸ 𝔪 ^ 2`, then `A ⧸ (f₁, …, f_c)` is again a regular local ring: the maximal
ideal of the quotient needs only `dim A - c` generators, while Krull's height theorem bounds
`dim A` by `dim (A ⧸ (f₁, …, f_c)) + c` from above.

## Main results

* `IsLocalRing.exists_span_union_range_eq_maximalIdeal`: a family with linearly independent
  classes in the cotangent space can be completed to a generating family of the maximal ideal
  by `dim_κ (𝔪 ⧸ 𝔪 ^ 2) - c` further elements.
* `IsRegularLocalRing.quotient_span_range`: the quotient of a regular local ring by such a
  family is regular local.
* `IsRegularRing.quotient_of_forall_isRegularLocalRing`: a criterion for `R ⧸ I` to be a regular
  ring in terms of the quotients of the localizations of `R` at the primes containing `I`.
-/

@[expose] public section

open IsLocalRing Submodule

namespace IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A finite family in the maximal ideal of a Noetherian local ring whose classes in the
cotangent space are linearly independent extends to a generating family of the maximal ideal
by adjoining `dim_κ (𝔪 ⧸ 𝔪 ^ 2) - #σ` further elements. -/
theorem exists_span_union_range_eq_maximalIdeal
    {σ : Type*} [Fintype σ] (f : σ → A) (hmem : ∀ i, f i ∈ maximalIdeal A)
    (hli : LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩)) :
    ∃ T : Set A, T.Finite ∧
      T.ncard + Fintype.card σ ≤ Module.finrank (ResidueField A) (CotangentSpace A) ∧
      Ideal.span (T ∪ Set.range f) = maximalIdeal A := by
  set K := ResidueField A
  set V := CotangentSpace A
  set v : σ → V := fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩
  have hinj : Function.Injective v := hli.injective
  have hli' : LinearIndepOn K id (Set.range v) := (linearIndepOn_range_iff hinj id).mpr hli
  set b := hli'.extend (Set.subset_univ _)
  have hsub : Set.range v ⊆ b := hli'.subset_extend _
  have hspan : Submodule.span K b = ⊤ := by
    simpa using hli'.span_extend_eq_span (Set.subset_univ _)
  have hbas : Module.Basis b K V := Module.Basis.extend hli'
  have hcard : b.ncard = Module.finrank K V := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    exact (Module.finrank_eq_card_basis hbas).symm
  choose g hg using Ideal.toCotangent_surjective (maximalIdeal A)
  set s : Set (maximalIdeal A) :=
    Set.range (fun i ↦ (⟨f i, hmem i⟩ : maximalIdeal A)) ∪ g '' (b \ Set.range v) with hs
  have himg : (maximalIdeal A).toCotangent '' s = b := by
    rw [hs, Set.image_union, ← Set.range_comp, ← Set.image_comp]
    have h1 : (maximalIdeal A).toCotangent ∘ (fun i ↦ (⟨f i, hmem i⟩ : maximalIdeal A)) = v := rfl
    have h2 : ∀ x ∈ b \ Set.range v, ((maximalIdeal A).toCotangent ∘ g) x = x := fun x _ ↦ hg x
    rw [h1, Set.image_congr h2]
    simpa using Set.union_sdiff_cancel hsub
  have hspans : Submodule.span A s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff, himg, hspan]
  have key : Ideal.span ((↑) '' s) = maximalIdeal A := by
    have := congrArg (Submodule.map (Submodule.subtype (maximalIdeal A))) hspans
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
  have himg2 : ((↑) : maximalIdeal A → A) '' s
      = (fun x ↦ ((g x : maximalIdeal A) : A)) '' (b \ Set.range v) ∪ Set.range f := by
    rw [hs, Set.image_union, ← Set.range_comp, ← Set.image_comp, Set.union_comm]
    rfl
  have hbfin : b.Finite := Set.toFinite b
  refine ⟨_, hbfin.sdiff.image _, ?_, himg2 ▸ key⟩
  have hrv : (Set.range v).ncard = Fintype.card σ := by
    rw [Set.ncard_range_of_injective (f := v) hinj, Nat.card_eq_fintype_card]
  have h3 : (b \ Set.range v).ncard = b.ncard - Fintype.card σ := by
    rw [Set.ncard_sdiff hsub, hrv]
  have h4 : Fintype.card σ ≤ b.ncard := by
    rw [← hrv]; exact Set.ncard_le_ncard hsub hbfin
  calc ((fun x ↦ ((g x : maximalIdeal A) : A)) '' (b \ Set.range v)).ncard + Fintype.card σ
      ≤ (b \ Set.range v).ncard + Fintype.card σ := by
        gcongr; exact Set.ncard_image_le hbfin.sdiff
    _ = Module.finrank K V := by rw [h3, ← hcard]; omega

end IsLocalRing

/-- **Cutting down a regular local ring.**  If the classes of a finite family `f` in the
cotangent space of a regular local ring `A` are linearly independent, then `A ⧸ (f)` is again
a regular local ring. -/
theorem IsRegularLocalRing.quotient_span_range {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {σ : Type*} [Finite σ] (f : σ → A) (hmem : ∀ i, f i ∈ maximalIdeal A)
    (hli : LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩)) :
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range f)) := by
  have : Fintype σ := Fintype.ofFinite σ
  set I : Ideal A := Ideal.span (Set.range f)
  have hIle : I ≤ maximalIdeal A := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hIle
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨T, hTfin, hT1, hT2⟩ := IsLocalRing.exists_span_union_range_eq_maximalIdeal f hmem hli
  have hmax : maximalIdeal (A ⧸ I) = Ideal.span (Ideal.Quotient.mk I '' T) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hT2,
      Ideal.map_span, Set.image_union, Ideal.span_union]
    refine sup_eq_left.mpr ?_
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hz : (Ideal.Quotient.mk I) (f i) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [hz]
    exact Submodule.zero_mem _
  have hsf : (maximalIdeal (A ⧸ I)).spanFinrank ≤ T.ncard := by
    rw [hmax]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hTfin.image _)).trans
      (Set.ncard_image_le hTfin)
  have hIsf : I.spanFinrank ≤ Fintype.card σ := by
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans ?_
    simpa using Set.ncard_image_le (Set.finite_univ (α := σ))
  have hdim : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + I.spanFinrank := by
    refine ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I (hIle.trans ?_)
    rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal (R := A) ⊥ bot_ne_top]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  have hreg : ringKrullDim A = (Module.finrank (ResidueField A) (CotangentSpace A) : ℕ) := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace A,
      IsRegularLocalRing.spanFinrank_maximalIdeal]
  rw [← ENat.WithBot.add_le_add_natCast_right_iff (c := Fintype.card σ)]
  calc ((maximalIdeal (A ⧸ I)).spanFinrank : WithBot ℕ∞) + Fintype.card σ
      ≤ ((T.ncard + Fintype.card σ : ℕ) : WithBot ℕ∞) := by push_cast; gcongr
    _ ≤ ringKrullDim A := by rw [hreg]; exact_mod_cast hT1
    _ ≤ ringKrullDim (A ⧸ I) + I.spanFinrank := hdim
    _ ≤ ringKrullDim (A ⧸ I) + Fintype.card σ := by gcongr

/-- To check that `R ⧸ I` is a regular ring it suffices to check, for every prime `Q` of `R`
containing `I`, that the quotient of `R` localised at `Q` by the ideal generated by `I` is a
regular local ring. -/
theorem IsRegularRing.quotient_of_forall_isRegularLocalRing {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R)
    (H : ∀ (Q : Ideal R) (_ : Q.IsPrime), I ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))) :
    IsRegularRing (R ⧸ I) := by
  rw [isRegularRing_iff]
  intro 𝔮 h𝔮
  have hQ : (𝔮.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ 𝔮
  have hIle : I ≤ 𝔮.comap (Ideal.Quotient.mk I) := fun x hx ↦ by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hmon : Algebra.algebraMapSubmonoid (R ⧸ I) (𝔮.comap (Ideal.Quotient.mk I)).primeCompl
      = 𝔮.primeCompl := by
    ext x
    refine ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun hx ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, hx, rfl⟩
  have hloc : IsLocalization 𝔮.primeCompl
      (Localization.AtPrime (𝔮.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap R (Localization.AtPrime (𝔮.comap (Ideal.Quotient.mk I))))) := by
    rw [← hmon]
    infer_instance
  have := H _ hQ hIle
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime (𝔮.comap (Ideal.Quotient.mk I)) ⧸
      I.map (algebraMap R (Localization.AtPrime (𝔮.comap (Ideal.Quotient.mk I)))))
    (IsLocalization.algEquiv 𝔮.primeCompl _ (Localization.AtPrime 𝔮)).toRingEquiv
