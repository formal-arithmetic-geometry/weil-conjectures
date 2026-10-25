/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BlowupRestriction
public import WeilConjectures.TraceFormula.BlowupRestrictionCurve
public import WeilConjectures.RingTheory.BlowupChartData
public import WeilConjectures.AlgebraicGeometry.RegularDivisorSpec

/-!
# The blown-up configuration in a chart

Let `R` be a local ring with a chart `R[T]/(xT - y)` of the blow-up of `T = Spec R` at its closed
point as in `AlgebraicGeometry.BlowupChartData` (`f = x^d f'`, `h = x h'`). Put
`Z = Spec (R[T]/(xT - y))[1/f']`, `Y = V(x) ⊆ Z` (the exceptional divisor off the strict transform
`D'` of `D = V(f)`) and `X = V(h') ⊆ Z` (the strict transform of `H = V(h)`). This file constructs
the transverse configuration of blueprint `det-tf-blowup-configuration`, in the chart:

* `X`, `Y` are regular divisors of `Z` meeting transversely at one point, `Y` is connected
  (`det-tf-blowup-configuration` (1));
* the blow-up map restricts to `φ : Z - Y ⟶ T - D` with `φ⁻¹(T - (D ∪ H)) = Z - (X ∪ Y)`
  (`det-tf-blowup-configuration` (2), (3); in the chart, `φ` is an isomorphism onto
  `T - (D ∪ V(x))`).

## Main definitions

- `AlgebraicGeometry.BlowupChartData.φ`: the blow-up map `Z - Y ⟶ T - D`.
- `AlgebraicGeometry.BlowupChartData.φU`: its restriction `Z - (X ∪ Y) ⟶ T - (D ∪ H)`.

## Main results

- `AlgebraicGeometry.BlowupChartData.isPullback_φ`: `φ⁻¹(T - (D ∪ H)) = Z - (X ∪ Y)`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.BlowupChartData

variable {R : Type u} [CommRing R] [IsLocalRing R] {f g h x₀ y₀ : R} {K : Type v} {c : K → R}
  (D : BlowupChartData f g h x₀ y₀ c)

/-- A point `y` of `V` lies in the image of `U ⊆ V` iff it lies in `U`. -/
lemma mem_range_homOfLE {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V) (y : V) :
    y ∈ Set.range (X.homOfLE e) ↔ y.1 ∈ U :=
  ⟨by rintro ⟨x, rfl⟩; simp, fun hy ↦ ⟨⟨y.1, hy⟩, Subtype.ext (by simp)⟩⟩

/-- The parameter `x = x₀ + c i y₀` of the chart. -/
abbrev x : R := x₀ + c D.i * y₀

/-- The coordinate ring `(R[T]/(xT - y))[1/f']` of `Z`, the chart minus the strict transform of
`D`. -/
abbrev Rx : Type u := Localization.Away D.f'

/-- The equation `x` of the exceptional divisor `Y` on `Z`. -/
noncomputable abbrev xx : D.Rx := algebraMap R D.Rx D.x

/-- The equation `h'` of the strict transform `X` of `H` on `Z`. -/
noncomputable abbrev hh : D.Rx := algebraMap (blowupChart D.x y₀) D.Rx D.h'

/-- `Z - Y`, the basic open of `x`. -/
noncomputable abbrev UY : (Spec (.of D.Rx)).Opens := PrimeSpectrum.basicOpen D.xx

/-- `Z - (X ∪ Y)`, the basic open of `x h'`. -/
noncomputable abbrev UXY : (Spec (.of D.Rx)).Opens := PrimeSpectrum.basicOpen (D.xx * D.hh)

lemma UXY_le_UY : D.UXY ≤ D.UY := PrimeSpectrum.basicOpen_mul_le_left _ _

/-- The image of `f` on `Z` is `x^d` times a unit. -/
lemma algebraMap_f_eq : algebraMap R D.Rx f = D.xx ^ D.d * algebraMap _ D.Rx D.f' := by
  rw [IsScalarTower.algebraMap_apply R (blowupChart D.x y₀) D.Rx, D.algebraMap_f, map_mul,
    map_pow, ← IsScalarTower.algebraMap_apply]

/-- The image of `h` on `Z` is `x h'`. -/
lemma algebraMap_h_eq : algebraMap R D.Rx h = D.xx * D.hh := by
  rw [IsScalarTower.algebraMap_apply R (blowupChart D.x y₀) D.Rx, D.algebraMap_h, map_mul,
    ← IsScalarTower.algebraMap_apply]

lemma isUnit_f' : IsUnit (algebraMap (blowupChart D.x y₀) D.Rx D.f') :=
  IsLocalization.Away.algebraMap_isUnit _

/-- The blow-up map sends `Z - Y` into `T - D`. -/
lemma range_subset_basicOpen_f :
    Set.range (D.UY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx))) ⊆
      Set.range (Scheme.specBasicOpen f).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f ∉ Ideal.comap (algebraMap R D.Rx) p.val.asIdeal
  rw [Ideal.mem_comap, D.algebraMap_f_eq]
  intro hp
  rcases p.val.isPrime.mem_or_mem hp with hx | hu
  · exact p.2 (p.val.isPrime.mem_of_pow_mem _ hx)
  · exact p.val.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu D.isUnit_f')

/-- The blow-up map `φ : Z - Y ⟶ T - D`. -/
noncomputable def φ : D.UY.toScheme ⟶ (Scheme.specBasicOpen f).toScheme :=
  IsOpenImmersion.lift _ _ D.range_subset_basicOpen_f

@[reassoc (attr := simp)]
lemma φ_ι : D.φ ≫ (Scheme.specBasicOpen f).ι =
    D.UY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The blow-up map sends `Z - (X ∪ Y)` into `T - (D ∪ H)`. -/
lemma range_subset_basicOpen_fh :
    Set.range (D.UXY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx))) ⊆
      Set.range (Scheme.specBasicOpen (f * h)).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f * h ∉ Ideal.comap (algebraMap R D.Rx) p.val.asIdeal
  rw [Ideal.mem_comap, map_mul, D.algebraMap_f_eq, D.algebraMap_h_eq]
  intro hp
  have hxh : D.xx * D.hh ∉ p.val.asIdeal := p.2
  rcases p.val.isPrime.mem_or_mem hp with hp | hp
  · rcases p.val.isPrime.mem_or_mem hp with hx | hu
    · exact hxh (Ideal.mul_mem_right _ _ (p.val.isPrime.mem_of_pow_mem _ hx))
    · exact p.val.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu D.isUnit_f')
  · exact hxh hp

/-- The restriction `φU : Z - (X ∪ Y) ⟶ T - (D ∪ H)` of the blow-up map. -/
noncomputable def φU : D.UXY.toScheme ⟶ (Scheme.specBasicOpen (f * h)).toScheme :=
  IsOpenImmersion.lift _ _ D.range_subset_basicOpen_fh

@[reassoc (attr := simp)]
lemma φU_ι : D.φU ≫ (Scheme.specBasicOpen (f * h)).ι =
    D.UXY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- `φ⁻¹(T - (D ∪ H)) = Z - (X ∪ Y)` (blueprint `det-tf-blowup-configuration` (2)). -/
lemma isPullback_φ :
    IsPullback D.φU ((Spec (.of D.Rx)).homOfLE D.UXY_le_UY)
      ((Spec (.of R)).homOfLE (PrimeSpectrum.basicOpen_mul_le_left f h)) D.φ := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [← cancel_mono (Scheme.specBasicOpen f).ι]
    simp
  · ext p
    change D.φ p ∈ Set.range ((Spec (.of R)).homOfLE _) ↔
      p ∈ Set.range ((Spec (.of D.Rx)).homOfLE D.UXY_le_UY)
    rw [mem_range_homOfLE, mem_range_homOfLE]
    have hφp : (D.φ p).1 = Spec.map (CommRingCat.ofHom (algebraMap R D.Rx)) p.1 := by
      rw [← Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, D.φ_ι, Scheme.Hom.comp_apply]
      rfl
    rw [hφp]
    change f * h ∉ Ideal.comap (algebraMap R D.Rx) p.val.asIdeal ↔ D.xx * D.hh ∉ p.val.asIdeal
    have hx : D.xx ∉ p.val.asIdeal := p.2
    rw [Ideal.mem_comap, map_mul, D.algebraMap_f_eq, D.algebraMap_h_eq, not_iff_not]
    constructor
    · intro hp
      rcases p.val.isPrime.mem_or_mem hp with hp | hp
      · rcases p.val.isPrime.mem_or_mem hp with hx' | hu
        · exact absurd (p.val.isPrime.mem_of_pow_mem _ hx') hx
        · exact absurd (Ideal.eq_top_of_isUnit_mem _ hu D.isUnit_f') p.val.isPrime.ne_top
      · exact hp
    · intro hp
      exact Ideal.mul_mem_left _ _ hp

end AlgebraicGeometry.BlowupChartData
