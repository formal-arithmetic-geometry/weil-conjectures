/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Functoriality

/-!

# The affine blow-up commutes with localization

For a localization `B = A[1/s]` and `J = I·B`, we show that the induced morphism
`blowupHom : AffineBlowup J ⟶ AffineBlowup I` exhibits `AffineBlowup J` as the pullback of
`AffineBlowup I` along `Spec B ⟶ Spec A`. The mathematical core is the chart-wise statement
`AffineBlowup.isLocalization_away_map`: on the chart at `a·X`, the induced map of chart
rings is the localization away from (the image of) `s`.

## Main results

- `AlgebraicGeometry.AffineBlowup.isLocalization_away_map` — chart-wise localization
  (blueprint: `prop:nagata-rees-localization`, in chart form).
- `AlgebraicGeometry.isPullback_blowupHom_of_isLocalization` — the blow-up square of a
  localization map is a pullback (blueprint: `prop:nagata-affine-blowup-restrict`).

-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

section Helpers

variable {R : Type u} [CommRing R]

private lemma monomial_congr {m n : ℕ} {x y : R} (hmn : m = n) (hxy : x = y) :
    Polynomial.monomial m x = Polynomial.monomial n y := by
  subst hmn; subst hxy; rfl

private lemma monomial_inj_of_eq {m n : ℕ} {x y : R}
    (h : Polynomial.monomial m x = Polynomial.monomial n y) (hmn : m = n) : x = y := by
  subst hmn
  exact Polynomial.monomial_injective m h

variable {I : Ideal R}

private lemma mem_pow_zero (r : R) : r ∈ I ^ 0 := by
  rw [pow_zero, Ideal.one_eq_top]
  trivial

/-- `val` of the canonical map `A →+* Away (reesGrading I) x` in monomial normal form. -/
private lemma val_awayAlgebraMap (x : reesAlgebra I) (r : R) :
    (AffineBlowup.awayAlgebraMap I x r).val =
      Localization.mk (reesMonomial I (n := 0) r (mem_pow_zero r)) 1 :=
  rfl

/-- Congruence for localization fractions with monomial numerators. -/
private lemma mk_reesMonomial_eq {M : Submonoid (reesAlgebra I)} {m n : ℕ} {x y : R}
    {hx : x ∈ I ^ m} {hy : y ∈ I ^ n} {d e : M} (hmn : m = n) (hxy : x = y)
    (hde : (d : reesAlgebra I) = (e : reesAlgebra I)) :
    Localization.mk (reesMonomial I x hx) d = Localization.mk (reesMonomial I y hy) e := by
  subst hmn; subst hxy
  obtain rfl : d = e := Subtype.ext hde
  rfl

end Helpers

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (s : A)
  [IsLocalization.Away s B] {I : Ideal A} {J : Ideal B}

include s

/-- **Chart-wise localization**: if `B = A[1/s]` and `J = I·B`, then on the chart at a
degree-one element `a·X` the induced map of chart rings
`Away (reesGrading I) (a·X) →+* Away (reesGrading J) (φ(a)·X)` is the localization away
from the image of `s`. (blueprint: `prop:nagata-rees-localization`, chart form) -/
theorem AffineBlowup.isLocalization_away_map (h : I.map (algebraMap A B) = J) (a : A)
    (ha : a ∈ I) :
    letI := (HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h)
      (reesX I a ha)).toAlgebra
    IsLocalization.Away (AffineBlowup.awayAlgebraMap I (reesX I a ha) s)
      (HomogeneousLocalization.Away (reesGrading J)
        (reesHom (algebraMap A B) h (reesX I a ha))) := by
  have hψ : HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h) (reesX I a ha)
        (AffineBlowup.awayAlgebraMap I (reesX I a ha) s) =
      AffineBlowup.awayAlgebraMap J (reesHom (algebraMap A B) h (reesX I a ha))
        (algebraMap A B s) := by
    simpa only [RingHom.coe_comp, Function.comp_apply] using
      RingHom.congr_fun (awayMap_awayAlgebraMap (algebraMap A B) h (reesX I a ha)) s
  letI := (HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h)
    (reesX I a ha)).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- units are mapped to units
    rintro ⟨y, n, rfl⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, hψ]
    exact (((IsLocalization.Away.algebraMap_isUnit (S := B) s).map
      (AffineBlowup.awayAlgebraMap J (reesHom (algebraMap A B) h (reesX I a ha))))).pow n
  · -- surjectivity up to multiplication with a power of `s`
    intro z
    obtain ⟨n, y, hy, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (reesGrading J)
        ((reesHom (algebraMap A B) h).map_mem (reesX_mem I a ha)) z
    obtain ⟨b, hb, rfl⟩ := (mem_reesGrading_iff_exists J).mp hy
    have hb' : b ∈ (I ^ (n • 1)).map (algebraMap A B) := by
      rw [Ideal.map_pow, h]
      exact hb
    obtain ⟨⟨⟨c, hc⟩, t⟩, ht⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) B).mp hb'
    obtain ⟨m, hm⟩ := t.2
    rw [← hm] at ht
    refine ⟨⟨HomogeneousLocalization.Away.mk (reesGrading I) (reesX_mem I a ha) n
      (reesMonomial I c hc) (reesMonomial_mem I c hc),
      ⟨AffineBlowup.awayAlgebraMap I (reesX I a ha) s ^ m, m, rfl⟩⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ext_iff_val]
    simp only [map_pow, hψ, val_mul, val_pow, HomogeneousLocalization.Away.map_mk,
      reesHom_reesMonomial, HomogeneousLocalization.Away.val_mk, val_awayAlgebraMap,
      Localization.mk_pow, one_pow, reesMonomial_pow, Localization.mk_mul, mul_one,
      reesMonomial_mul]
    exact mk_reesMonomial_eq (by simp) (by rw [← map_pow]; exact ht) rfl
  · -- elements with the same image differ by a power of `s`
    intro z₁ z₂ hz
    rw [RingHom.algebraMap_toAlgebra] at hz
    obtain ⟨n₁, y₁, hy₁, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (reesGrading I) (reesX_mem I a ha) z₁
    obtain ⟨n₂, y₂, hy₂, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (reesGrading I) (reesX_mem I a ha) z₂
    obtain ⟨c₁, hc₁, rfl⟩ := (mem_reesGrading_iff_exists I).mp hy₁
    obtain ⟨c₂, hc₂, rfl⟩ := (mem_reesGrading_iff_exists I).mp hy₂
    rw [ext_iff_val] at hz
    simp only [HomogeneousLocalization.Away.map_mk, reesHom_reesMonomial,
      HomogeneousLocalization.Away.val_mk] at hz
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hz
    obtain ⟨⟨t, k, rfl⟩, ht⟩ := hz
    have ht' := congrArg (fun F : reesAlgebra J => (F : Polynomial B)) ht
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_reesHom_apply, coe_reesX,
      Polynomial.map_monomial, coe_reesMonomial, Polynomial.monomial_pow,
      Polynomial.monomial_mul_monomial, one_mul, Nat.nsmul_eq_mul, mul_one] at ht'
    have key := monomial_inj_of_eq ht' (by omega)
    have hker : algebraMap A B (a ^ (k + n₂) * c₁ - a ^ (k + n₁) * c₂) = 0 := by
      simp only [map_sub, map_mul, map_pow, pow_add]
      linear_combination key
    obtain ⟨⟨t', m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers s) B _).mp hker
    refine ⟨⟨AffineBlowup.awayAlgebraMap I (reesX I a ha) s ^ m, m, rfl⟩, ?_⟩
    rw [ext_iff_val]
    simp only [val_mul, val_pow, val_awayAlgebraMap, HomogeneousLocalization.Away.val_mk,
      Localization.mk_pow, one_pow, reesMonomial_pow, Localization.mk_mul, one_mul,
      reesMonomial_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨⟨reesX I a ha ^ k, k, rfl⟩, ?_⟩
    refine Subtype.ext ?_
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_reesX, coe_reesMonomial,
      Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul, Nat.nsmul_eq_mul,
      mul_one, zero_mul, zero_add]
    exact monomial_congr (by omega) (by linear_combination hm)

/-- Chart-level open immersion: `Spec` of the induced map of chart rings is an open
immersion. -/
lemma AffineBlowup.isOpenImmersion_SpecMap_awayMap (h : I.map (algebraMap A B) = J)
    (a : A) (ha : a ∈ I) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h) (reesX I a ha)))) := by
  letI := (HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h)
    (reesX I a ha)).toAlgebra
  haveI : IsLocalization.Away (AffineBlowup.awayAlgebraMap I (reesX I a ha) s)
      (HomogeneousLocalization.Away (reesGrading J)
        (reesHom (algebraMap A B) h (reesX I a ha))) :=
    AffineBlowup.isLocalization_away_map s h a ha
  exact IsOpenImmersion.of_isLocalization (AffineBlowup.awayAlgebraMap I (reesX I a ha) s)

/-- Chart-level range formula for the induced map of chart rings. -/
lemma AffineBlowup.opensRange_SpecMap_awayMap (h : I.map (algebraMap A B) = J)
    (a : A) (ha : a ∈ I) :
    haveI := AffineBlowup.isOpenImmersion_SpecMap_awayMap (B := B) s h a ha
    (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h)
          (reesX I a ha)))).opensRange =
      PrimeSpectrum.basicOpen (AffineBlowup.awayAlgebraMap I (reesX I a ha) s) := by
  letI := (HomogeneousLocalization.Away.map (reesHom (algebraMap A B) h)
    (reesX I a ha)).toAlgebra
  haveI : IsLocalization.Away (AffineBlowup.awayAlgebraMap I (reesX I a ha) s)
      (HomogeneousLocalization.Away (reesGrading J)
        (reesHom (algebraMap A B) h (reesX I a ha))) :=
    AffineBlowup.isLocalization_away_map s h a ha
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (HomogeneousLocalization.Away (reesGrading J)
      (reesHom (algebraMap A B) h (reesX I a ha)))
    (AffineBlowup.awayAlgebraMap I (reesX I a ha) s)

variable (B)

/-- The blow-up morphism induced by a localization map is an open immersion. -/
theorem isOpenImmersion_blowupHom_of_isLocalization (h : I.map (algebraMap A B) = J) :
    IsOpenImmersion (blowupHom (algebraMap A B) h) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsOpenImmersion) _
    (AffineBlowup.iSup_basicOpen_reesX_eq_top I)]
  intro a
  have w := chart_blowupHom (algebraMap A B) h (reesX I a a.2) (reesX_mem I a a.2)
  have hpre : blowupHom (algebraMap A B) h ⁻¹ᵁ
      (AffineBlowup.chart I (reesX I a a.2) (reesX_mem I a a.2)).opensRange =
      (AffineBlowup.chart J (reesHom (algebraMap A B) h (reesX I a a.2))
        ((reesHom (algebraMap A B) h).map_mem (reesX_mem I a a.2))).opensRange := by
    rw [AffineBlowup.opensRange_chart, AffineBlowup.opensRange_chart]
    rfl
  rw [← AffineBlowup.opensRange_chart I (reesX I a a.2) (reesX_mem I a a.2),
    MorphismProperty.arrow_mk_iso_iff (P := @IsOpenImmersion)
      (morphismRestrictArrowIso (blowupHom (algebraMap A B) h)
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
          (reesHom (algebraMap A B) h) (reesX I a a.2)))) w hpre)]
  exact AffineBlowup.isOpenImmersion_SpecMap_awayMap s h a a.2

/-- The range of the blow-up morphism induced by a localization map is the preimage of the
range of `Spec B ⟶ Spec A` under the structure morphism. -/
theorem opensRange_blowupHom_of_isLocalization (h : I.map (algebraMap A B) = J) :
    haveI := isOpenImmersion_blowupHom_of_isLocalization B s h
    haveI := IsOpenImmersion.of_isLocalization (S := B) s
    (blowupHom (algebraMap A B) h).opensRange =
      AffineBlowup.toSpec I ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).opensRange := by
  haveI := isOpenImmersion_blowupHom_of_isLocalization B s h
  haveI := IsOpenImmersion.of_isLocalization (S := B) s
  have hV : (Spec.map (CommRingCat.ofHom (algebraMap A B))).opensRange =
      PrimeSpectrum.basicOpen s := by
    rw [SetLike.ext'_iff]
    exact PrimeSpectrum.localization_away_comap_range B s
  refine Scheme.Opens.ext_of_openCover
    (Proj.affineOpenCoverOfIrrelevantLESpan (reesGrading I)
      (fun a : I ↦ reesX I a a.2) (fun a ↦ reesX_mem I a a.2) (fun _ ↦ one_pos)
      (irrelevant_le_span_range_reesX I)).openCover (fun (a : I) ↦ ?_)
  change AffineBlowup.chart I (reesX I a a.2) (reesX_mem I a a.2) ⁻¹ᵁ _ =
    AffineBlowup.chart I (reesX I a a.2) (reesX_mem I a a.2) ⁻¹ᵁ _
  haveI := AffineBlowup.isOpenImmersion_SpecMap_awayMap (B := B) s h a a.2
  rw [← (isPullback_chart_blowupHom (algebraMap A B) h (reesX I a a.2)
      (reesX_mem I a a.2)).opensRange_fst,
    AffineBlowup.opensRange_SpecMap_awayMap s h a a.2, ← Scheme.Hom.comp_preimage,
    AffineBlowup.chart_toSpec, hV, SpecMap_preimage_basicOpen]
  rfl

/-- **The affine blow-up commutes with localization**: for `B = A[1/s]` and `J = I·B`, the
blow-up square is a pullback. (blueprint: `prop:nagata-affine-blowup-restrict`) -/
theorem isPullback_blowupHom_of_isLocalization (h : I.map (algebraMap A B) = J) :
    IsPullback (blowupHom (algebraMap A B) h) (AffineBlowup.toSpec J)
      (AffineBlowup.toSpec I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  haveI := isOpenImmersion_blowupHom_of_isLocalization B s h
  haveI := IsOpenImmersion.of_isLocalization (S := B) s
  exact (IsOpenImmersion.isPullback (AffineBlowup.toSpec J) (blowupHom (algebraMap A B) h)
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) (AffineBlowup.toSpec I)
    (blowupHom_toSpec (algebraMap A B) h)
    (opensRange_blowupHom_of_isLocalization B s h).symm).flip

end AlgebraicGeometry
