/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.Principalization
public import WeilConjectures.Mathlib.RingTheory.Ideal.Span

/-!

# Slopes on the affine blow-up charts

For `a, b ∈ I`, the chart `Spec A[I/a]` of the blow-up of `I` carries the *slope* `b/a`,
the degree-one fraction `(b·X)/(a·X)` of the Rees algebra. This file provides the
algebraic kit for slopes.

## Main definitions

- `AlgebraicGeometry.AffineBlowup.awaySlope` — the slope `b/a` on the `a`-chart.

## Main results

- `AlgebraicGeometry.AffineBlowup.awaySlope_mul_awayAlgebraMap` — clearing the
  denominator: `(b/a) · a = b` in the chart ring;
- `AlgebraicGeometry.AffineBlowup.one_mem_span_awaySlope` — the slopes of a generating
  family of `I` generate the unit ideal of the chart ring;
- `AlgebraicGeometry.AffineBlowup.awayMap_awaySlope_eq` — the transition formula between
  two charts, in the exact-identity form `c · b = c' · a`;
- `AlgebraicGeometry.AffineBlowup.isPullback_chart` — the chart at a product `a · b` of
  two degree-one Rees elements is the intersection of the `a`-chart and the `b`-chart;
- `AlgebraicGeometry.AffineBlowup.chart_preimage_opensRange` — that intersection is the
  basic open of the slope `b/a` inside the `a`-chart.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry.AffineBlowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The slope `b/a` on the `a`-chart of the blow-up of `I`: the degree-one fraction
`(b·X)/(a·X)` of the Rees algebra of `I`. -/
def awaySlope {a : A} (ha : a ∈ I) {b : A} (hb : b ∈ I) :
    Away (reesGrading I) (reesX I a ha) :=
  HomogeneousLocalization.Away.mk (reesGrading I) (reesX_mem I a ha) 1 (reesX I b hb)
    (by simpa using reesX_mem I b hb)

variable {I}

/-- The slope `a/a` is `1`. -/
lemma awaySlope_self {a : A} (ha : a ∈ I) : awaySlope I ha ha = 1 := by
  rw [HomogeneousLocalization.ext_iff_val, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp [pow_one]⟩

/-- The slope of the zero numerator is `0`. -/
lemma awaySlope_zero {a : A} (ha : a ∈ I) (h0 : (0 : A) ∈ I) :
    awaySlope I ha h0 = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_zero]
  have h : reesX I 0 h0 = 0 := Subtype.ext (by simp)
  rw [h, Localization.mk_zero]

/-- Slopes are additive in the numerator. -/
lemma awaySlope_add {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hbc : b + c ∈ I) : awaySlope I ha hbc = awaySlope I ha hb + awaySlope I ha hc := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add, awaySlope,
    awaySlope, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.add_mk_self, reesX_add I hb hc]

/-- Slopes absorb ring multiples of the numerator through the structure map of the
chart ring. -/
lemma awaySlope_mul_left {a b : A} (r : A) (ha : a ∈ I) (hb : b ∈ I) (hrb : r * b ∈ I) :
    awaySlope I ha hrb = awayAlgebraMap I (reesX I a ha) r * awaySlope I ha hb := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, awaySlope,
    awaySlope, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    val_awayAlgebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial]

/-- Clearing the denominator of a slope: `(b/a) · a = b` in the chart ring. -/
lemma awaySlope_mul_awayAlgebraMap {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    awaySlope I ha hb * awayAlgebraMap I (reesX I a ha) a =
      awayAlgebraMap I (reesX I a ha) b := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, awaySlope,
    HomogeneousLocalization.Away.val_mk, val_awayAlgebraMap, val_awayAlgebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [mul_comm]

/-- **The slopes of a generating family generate the unit ideal of the chart ring.**
If `gen` generates `I` and `a ∈ I`, then `1 ∈ (gen k / a : k)` in `A[I/a]`: writing
`a = Σ cₖ · gen k` and dividing by `a` exhibits `1 = a/a` as a combination of the
slopes. -/
lemma one_mem_span_awaySlope {κ : Type*} (gen : κ → A) (hgen : ∀ k, gen k ∈ I)
    (hspan : Ideal.span (Set.range gen) = I) {a : A} (ha : a ∈ I) :
    (1 : Away (reesGrading I) (reesX I a ha)) ∈
      Ideal.span (Set.range fun k ↦ awaySlope I ha (hgen k)) := by
  rw [← awaySlope_self ha]
  exact Ideal.mem_span_range_of_forall_mem (F := fun b hb ↦ awaySlope I ha hb)
    (c := awayAlgebraMap I (reesX I a ha))
    (fun h0 ↦ awaySlope_zero ha h0)
    (fun {_ _} hx hy hxy ↦ awaySlope_add ha hx hy hxy)
    (fun r {_} hx hrx ↦ awaySlope_mul_left r ha hx hrx) hgen hspan ha

/-- The product of two slopes on the same chart depends only on the product of the
numerators. -/
lemma awaySlope_mul_awaySlope {a b b' d d' : A} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hd : d ∈ I) (hd' : d' ∈ I) (h : b * b' = d * d') :
    awaySlope I ha hb * awaySlope I ha hb' = awaySlope I ha hd * awaySlope I ha hd' := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mul, awaySlope, awaySlope, awaySlope, awaySlope,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial, h]

/-- The transition of a slope into the chart at a product: `(c/a)` maps to
`(c·b)/(a·b)` in `A[I/(a·b)]`-in-Rees-form. -/
lemma awayMap_awaySlope {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    {x : reesAlgebra I} (hx : x = reesX I a ha * reesX I b hb) :
    awayMap (reesGrading I) (reesX_mem I b hb) hx (awaySlope I ha hc) =
      HomogeneousLocalization.Away.mk (reesGrading I)
        (hx ▸ SetLike.mul_mem_graded (reesX_mem I a ha) (reesX_mem I b hb)) 1
        (reesX I c hc * reesX I b hb)
        (by simpa using SetLike.mul_mem_graded (reesX_mem I c hc) (reesX_mem I b hb)) := by
  rw [awaySlope, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [pow_one]

/-- **Chart transitions of slopes**: if `c · b = c' · a` in `A`, then the slope `c/a`
of the `a`-chart and the slope `c'/b` of the `b`-chart agree on the overlap
`A[I/(a·b)]`. This exact-identity form is what the elimination-of-indeterminacy
construction arranges by clearing denominators. -/
lemma awayMap_awaySlope_eq {a b c c' : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hc' : c' ∈ I) (h : c * b = c' * a) :
    awayMap (reesGrading I) (reesX_mem I b hb) rfl (awaySlope I ha hc) =
      awayMap (reesGrading I) (reesX_mem I a ha)
        (mul_comm (reesX I a ha) (reesX I b hb)) (awaySlope I hb hc') := by
  rw [awayMap_awaySlope ha hb hc rfl,
    awayMap_awaySlope hb ha hc' (mul_comm (reesX I a ha) (reesX I b hb)),
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial, h]

/-- **Composing the slopes across two charts**: on the chart at `a · d` the slope `b / d`
times the slope `d / a` is the slope `b / a`. -/
lemma awayMap_awaySlope_mul {a d b : A} (ha : a ∈ I) (hd : d ∈ I) (hb : b ∈ I) :
    awayMap (reesGrading I) (reesX_mem I a ha)
        (mul_comm (reesX I a ha) (reesX I d hd)) (awaySlope I hd hb) *
      awayMap (reesGrading I) (reesX_mem I d hd) rfl (awaySlope I ha hd) =
      awayMap (reesGrading I) (reesX_mem I d hd) rfl (awaySlope I ha hb) := by
  rw [awayMap_awaySlope hd ha hb (mul_comm (reesX I a ha) (reesX I d hd)),
    awayMap_awaySlope ha hd hd rfl, awayMap_awaySlope ha hd hb rfl,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one, Submonoid.coe_mul]
  ring

/-- The `Away.isLocalizationElem` of two degree-one Rees elements is the slope. -/
lemma isLocalizationElem_eq_awaySlope {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I a ha) (reesX_mem I b hb) =
      awaySlope I ha hb := by
  rw [HomogeneousLocalization.ext_iff_val, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, pow_one]

/-- **Passing between blow-up charts**: if the image of `b` is invertible at a point of the
`a`-chart, that point lies in the `b`-chart. -/
lemma mem_range_chart_of_mem_basicOpen {a b : A} (ha : a ∈ I) (hb : b ∈ I)
    (y : Spec (.of (HomogeneousLocalization.Away (reesGrading I) (reesX I a ha))))
    (hy : y ∈ PrimeSpectrum.basicOpen (awayAlgebraMap I (reesX I a ha) b)) :
    chart I (reesX I a ha) (reesX_mem I a ha) y ∈
      Set.range (chart I (reesX I b hb) (reesX_mem I b hb)) := by
  have hmem : y ∈ chart I (reesX I a ha) (reesX_mem I a ha) ⁻¹ᵁ
      Proj.basicOpen (reesGrading I) (reesX I b hb) := by
    rw [chart, Proj.awayι_preimage_basicOpen (𝒜 := reesGrading I)
      (reesX_mem I a ha) one_pos (reesX_mem I b hb) one_pos,
      isLocalizationElem_eq_awaySlope ha hb]
    have hfac : awayAlgebraMap I (reesX I a ha) b =
        awaySlope I ha hb * awayAlgebraMap I (reesX I a ha) a :=
      (awaySlope_mul_awayAlgebraMap ha hb).symm
    rw [hfac, PrimeSpectrum.basicOpen_mul] at hy
    exact hy.1
  rw [← opensRange_chart I (reesX I b hb) (reesX_mem I b hb)] at hmem
  exact hmem

/-- **The chart at a product of two degree-one Rees elements is the intersection of the two
charts.** The square

```
  Spec A[I/(a·b)] --awayMap--> Spec A[I/b]
        |                           |
  awayMap                        chart b
        |                           |
        v                           v
   Spec A[I/a] ----chart a----> AffineBlowup I
```

is a pullback square. -/
lemma isPullback_chart {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
        (reesX_mem I b hb) (rfl : reesX I a ha * reesX I b hb = reesX I a ha * reesX I b hb))))
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
        (reesX_mem I a ha) (mul_comm (reesX I a ha) (reesX I b hb)))))
      (chart I (reesX I a ha) (reesX_mem I a ha))
      (chart I (reesX I b hb) (reesX_mem I b hb)) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (Proj.pullbackAwayιIso (reesGrading I) (reesX_mem I a ha) one_pos (reesX_mem I b hb)
      one_pos (rfl : reesX I a ha * reesX I b hb = reesX I a ha * reesX I b hb)).symm
    ?_ ?_
  · rw [chart, chart, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
  · exact Proj.pullbackAwayιIso_inv_fst ..
  · exact Proj.pullbackAwayιIso_inv_snd (hx := rfl) ..

/-- The transition map into the chart at `a · b` has range the basic open of the slope
`b / a`. -/
lemma mem_range_specMap_awayMap_iff {a b : A} (ha : a ∈ I) (hb : b ∈ I)
    (y : Spec (.of (HomogeneousLocalization.Away (reesGrading I) (reesX I a ha)))) :
    (∃ z, Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
      (reesX_mem I b hb) (rfl : reesX I a ha * reesX I b hb = _))) z = y) ↔
      y ∈ PrimeSpectrum.basicOpen (awaySlope I ha hb) := by
  let := (HomogeneousLocalization.awayMap (reesGrading I) (reesX_mem I b hb)
    (rfl : reesX I a ha * reesX I b hb = _)).toAlgebra
  have := HomogeneousLocalization.Away.isLocalization_mul (reesX_mem I a ha)
    (reesX_mem I b hb) rfl one_ne_zero
  rw [← isLocalizationElem_eq_awaySlope]
  exact Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range _ _) y

/-- The `a`-chart of the blow-up meets the `b`-chart in the basic open of the slope `b / a`. -/
lemma chart_preimage_opensRange {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    chart I (reesX I a ha) (reesX_mem I a ha) ⁻¹ᵁ
        (chart I (reesX I b hb) (reesX_mem I b hb)).opensRange =
      PrimeSpectrum.basicOpen (awaySlope I ha hb) := by
  rw [opensRange_chart, chart,
    Proj.awayι_preimage_basicOpen (𝒜 := reesGrading I) (reesX_mem I a ha) one_pos
      (reesX_mem I b hb) one_pos, isLocalizationElem_eq_awaySlope]

end AlgebraicGeometry.AffineBlowup
