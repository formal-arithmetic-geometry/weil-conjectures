/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent

/-!
# Quotients of regular local rings and of regular rings

If `A` is a regular local ring and `f₁, …, f_c ∈ 𝔪` have linearly independent classes in the
cotangent space `𝔪 ⧸ 𝔪 ^ 2`, then `A ⧸ (f₁, …, f_c)` is again a regular local ring: the maximal
ideal of the quotient needs only `dim A - c` generators, while Krull's height theorem bounds
`dim A` by `dim (A ⧸ (f₁, …, f_c)) + c` from above.  Regularity of a quotient `R ⧸ I` of a
Noetherian ring can in turn be checked on the localizations of `R` at the primes containing `I`.

## Main results

* `IsRegularLocalRing.quotient_span_range`: the quotient of a regular local ring by such a
  family is regular local.
* `IsRegularLocalRing.quotient_span_singleton`: the case of a single element of `𝔪 \ 𝔪 ^ 2`.
* `IsRegularRing.quotient_of_forall_isRegularLocalRing`: a criterion for `R ⧸ I` to be a regular
  ring in terms of the quotients of the localizations of `R` at the primes containing `I`.
-/

@[expose] public section

open IsLocalRing

/-- **Cutting down a regular local ring.**  If the classes of a finite family `f` in the
cotangent space of a regular local ring `A` are linearly independent, then `A ⧸ (f)` is again
a regular local ring. -/
theorem IsRegularLocalRing.quotient_span_range {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {σ : Type*} [Finite σ] (f : σ → A) (hmem : ∀ i, f i ∈ maximalIdeal A)
    (hli : LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩)) :
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range f)) := by
  set I : Ideal A := Ideal.span (Set.range f)
  have hIle : I ≤ maximalIdeal A := Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
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
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩ : f i ∈ I)]
    exact Submodule.zero_mem _
  have hsf : (maximalIdeal (A ⧸ I)).spanFinrank ≤ T.ncard := by
    rw [hmax]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hTfin.image _)).trans
      (Set.ncard_image_le hTfin)
  have hIsf : I.spanFinrank ≤ Nat.card σ := by
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans ?_
    rw [← Set.image_univ, ← Set.ncard_univ σ]
    exact Set.ncard_image_le Set.finite_univ
  have hdim : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + I.spanFinrank := by
    refine ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I (hIle.trans ?_)
    rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal (R := A) ⊥ bot_ne_top]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  have hreg : ringKrullDim A = (Module.finrank (ResidueField A) (CotangentSpace A) : ℕ) := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace A,
      IsRegularLocalRing.spanFinrank_maximalIdeal]
  rw [← ENat.WithBot.add_le_add_natCast_right_iff (c := Nat.card σ)]
  calc ((maximalIdeal (A ⧸ I)).spanFinrank : WithBot ℕ∞) + Nat.card σ
      ≤ ((T.ncard + Nat.card σ : ℕ) : WithBot ℕ∞) := by
        push_cast
        gcongr
    _ ≤ ringKrullDim A := by
        rw [hreg]
        exact_mod_cast hT1
    _ ≤ ringKrullDim (A ⧸ I) + I.spanFinrank := hdim
    _ ≤ ringKrullDim (A ⧸ I) + Nat.card σ := by gcongr

/-- The quotient of a regular local ring by an element of `𝔪 \ 𝔪 ^ 2` is again regular local. -/
theorem IsRegularLocalRing.quotient_span_singleton {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {x : A} (hx : x ∈ maximalIdeal A) (hx2 : x ∉ maximalIdeal A ^ 2) :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) := by
  have hli : LinearIndependent (ResidueField A)
      (fun _ : Unit ↦ (maximalIdeal A).toCotangent ⟨x, hx⟩) := by
    refine (IsLocalRing.linearIndependent_toCotangent_iff (fun _ : Unit ↦ x)
      (fun _ ↦ hx)).mpr fun a ha i ↦ ?_
    rw [Fintype.sum_unique] at ha
    rw [Subsingleton.elim i default]
    by_contra hmem
    exact hx2 ((Ideal.unit_mul_mem_iff_mem _ (notMem_maximalIdeal.mp hmem)).mp ha)
  have := IsRegularLocalRing.quotient_span_range (fun _ : Unit ↦ x) (fun _ ↦ hx) hli
  rwa [Set.range_const] at this

/-- To check that `R ⧸ I` is a regular ring it suffices to check, for every prime `Q` of `R`
containing `I`, that the quotient of `R` localised at `Q` by the ideal generated by `I` is a
regular local ring. -/
theorem IsRegularRing.quotient_of_forall_isRegularLocalRing {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R)
    (H : ∀ (Q : Ideal R) [Q.IsPrime], I ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))) :
    IsRegularRing (R ⧸ I) := by
  rw [isRegularRing_iff]
  intro 𝔮 h𝔮
  set Q := 𝔮.comap (Ideal.Quotient.mk I) with hQdef
  have : Q.IsPrime := Ideal.comap_isPrime _ 𝔮
  set B := Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))
  have hIle : I ≤ Q := fun x hx ↦ by
    simp [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hmon : Algebra.algebraMapSubmonoid (R ⧸ I) Q.primeCompl = 𝔮.primeCompl := by
    ext x
    refine ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun hx ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, hx, rfl⟩
  have hloc : IsLocalization 𝔮.primeCompl B := by
    rw [← hmon]
    infer_instance
  have := H Q hIle
  exact IsRegularLocalRing.of_ringEquiv (R := B)
    (IsLocalization.algEquiv 𝔮.primeCompl _ (Localization.AtPrime 𝔮)).toRingEquiv
