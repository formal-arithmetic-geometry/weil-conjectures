/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.Paper.ConstructibleIntervals
public import Sheaf.Paper.PurityAffineChartCover
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Data.Finset.Lattice.Fold
import Sheaf.Paper.PurityChartLocalBounds
import Sheaf.Paper.PurityFiniteOpenIntervalDescent
import Sheaf.Paper.PurityOpenTensorTestVanishing
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-!
# Chartwise preservation for the constructible exceptional inverse image

Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
order 2078 (blueprint: thm-pur-general-admissibility).

The finite chart data include the actual closed presentations and their open complements.
Charts may be empty. Suprema in the natural numbers have value zero on the
empty family; consequently the empty-source case has D = c = 0.

## Main definitions and statements

- `Scheme.PurityAffineChartCover`: the finite affine covers and closed presentations.
- `PurityAffineChartCover.maxEmbeddingDimension` and `preservationConstant`: the maxima.
- `PurityFiniteSetting.general_admissibility`: the conditional two-clause preservation theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-! The chart-cover structure and its maxima are defined in
`Sheaf.Paper.PurityAffineChartCover`; this file states the preservation theorem. -/

namespace WeilConjectures.PurityFiniteSetting

private theorem interval_iff (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (hl : ∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x))
    (a b : ℤ) (hab : a ≤ b) (K : Scheme.proEtaleDerivedCategory X P.Ring) :
    Scheme.finiteTorsionConstructibleIn P.coefficients.l P.extension P.level P.level_pos
        X hl a b hab K ↔
      constructibleInterval P.coefficients.l P.extension P.level P.level_pos X a b K := by
  classical
  constructor
  · rintro ⟨hc, hv⟩
    exact ⟨hc, fun q hq ↦ by_contra fun hout ↦ hq (hv q hout)⟩
  · rintro ⟨hc, hs⟩
    exact ⟨hc, fun q hq ↦ by_contra fun hn ↦ hq (hs hn)⟩

private theorem chart_interval_bounds {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : Scheme.PurityAffineChartCover f)
    (cU : (v : Fin C.baseCount) → Fin (C.chartCount v) → ℕ)
    (v : Fin C.baseCount) (i : Fin (C.chartCount v)) (a b : ℤ) :
    a - 2 * (C.maxEmbeddingDimension : ℤ) ≤ a - 2 * (C.embeddingDimension v i : ℤ) ∧
    b - 2 * (C.embeddingDimension v i : ℤ) + (cU v i : ℤ) + 1 ≤
      b - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ) := by
  have hd : C.embeddingDimension v i ≤ C.maxEmbeddingDimension :=
    Finset.le_sup (f := fun t : (v : Fin C.baseCount) × Fin (C.chartCount v) ↦
      C.embeddingDimension t.1 t.2) (Finset.mem_univ ⟨v, i⟩)
  have hc : cU v i + 1 + 2 * (C.maxEmbeddingDimension - C.embeddingDimension v i) ≤
      C.preservationConstant cU :=
    Finset.le_sup (f := fun t : (v : Fin C.baseCount) × Fin (C.chartCount v) ↦
      cU t.1 t.2 + 1 + 2 * (C.maxEmbeddingDimension - C.embeddingDimension t.1 t.2))
      (Finset.mem_univ ⟨v, i⟩)
  have hd' : (C.embeddingDimension v i : ℤ) ≤ C.maxEmbeddingDimension := by
    exact_mod_cast hd
  have hc' : (cU v i : ℤ) + 1 +
      2 * ((C.maxEmbeddingDimension : ℤ) - (C.embeddingDimension v i : ℤ)) ≤
      (C.preservationConstant cU : ℤ) := by
    exact_mod_cast (show (cU v i : ℤ) + 1 +
      2 * ((C.maxEmbeddingDimension : ℤ) - (C.embeddingDimension v i : ℤ)) ≤
      (C.preservationConstant cU : ℤ) from by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
          Nat.cast_sub hd] using (Int.ofNat_le.mpr hc))
  constructor <;> omega

private theorem tor_mono {X : Scheme.{u}} {A : Type u} [CommRing A]
    {K : Scheme.proEtaleDerivedCategory X A} {a b r s : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude X A K a b) (hr : r ≤ a) (hs : b ≤ s) :
    Scheme.HasProEtaleTorAmplitude X A K r s := by
  refine ⟨le_trans hr (le_trans h.1 hs), ?_⟩
  intro L Q e f hf hQ M q hq
  apply h.2 L Q e f hf hQ M q
  rcases hq with hq | hq
  · exact Or.inl (lt_of_lt_of_le hq hr)
  · exact Or.inr (lt_of_le_of_lt hs hq)

private theorem zero_of_open_cover (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} {J : Type*} (U : J → X.Opens)
    (hcover : ∀ x : X, ∃ t, x ∈ U t)
    (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (hM : ∀ t, IsZero ((Scheme.proEtaleConstantRingPullback A (U t).ι).obj M)) :
    IsZero M := by
  let E := Scheme.proEtaleModuleRestriction X A
  let := Scheme.proEtaleModuleRestriction_isEquivalence X A
  have : E.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have hz : IsZero (E.obj M) :=
    ProEtale.isZero_of_forall_isZero_upperStar_obj
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U hcover _ (fun t ↦ by
        let := Scheme.proEtaleModuleRestriction_isEquivalence (U t).toScheme A
        have : (Scheme.proEtaleModuleRestriction (U t).toScheme A).Additive := by
          constructor
          intro M N f g
          ext V x
          rfl
        obtain ⟨e⟩ := Scheme.proEtaleModuleRestriction_pullback (U t).ι A M
        exact ((Scheme.proEtaleModuleRestriction (U t).toScheme A).map_isZero (hM t)).of_iso
          e.symm)
  apply (IsZero.iff_id_eq_zero M).mpr
  apply E.map_injective
  exact hz.eq_of_src _ _

private theorem tor_open_descent (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} {J : Type*} (U : J → X.Opens)
    (hcover : ∀ x : X, ∃ t, x ∈ U t)
    (K : Scheme.proEtaleDerivedCategory X A) (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ t, Scheme.HasProEtaleTorAmplitude (U t).toScheme A
      ((Scheme.proEtaleConstantRingDerivedPullback A (U t).ι).obj K) a b) :
    Scheme.HasProEtaleTorAmplitude X A K a b := by
  refine ⟨hab, ?_⟩
  intro L Q e f hf hQ M q hq
  apply zero_of_open_cover A U hcover
  intro t
  exact purityOpenTensorTestVanishing A (U t).ι K a b (hK t) L Q e f hf hQ M q hq

/-- Conditional preservation with exactly the chart maxima of the blueprint.
Source: blueprint order 2078 (blueprint: thm-pur-general-admissibility).

Proof:
1. Index all charts by the finite dependent sum J of their indices; the base cover and the
   chart covers show that the chart opens cover X (also when J is empty). For each chart,
   `Finset.le_sup` gives d_U ≤ D and c_U+1+2(D-d_U) ≤ c, so the chart interval
   [a-2d_U,b-2d_U+c_U+1] lies in [a-2D,b-2D+c].
2. `chart_local_bounds` (lem-pur-chart-local-bounds) gives the smooth-then-closed bounds on
   each chart. Enlarge them to the uniform interval and glue with
   `purityFiniteOpenIntervalDescent`. `finiteTorsionConstructibleIn` is equivalent to
   `constructibleInterval`; this proves the first conclusion.
3. For a Tor input, the chart Tor clause enlarged to the uniform interval and
   `purityOpenTensorTestVanishing` make every global tensor test vanish after restriction
   to each chart. Restriction to constant scalars is a faithful additive equivalence
   commuting with open pullback, so the open-cover zero test gives the global Tor interval.
4. A bounded constructible input has its support in some interval [min p q, q]; the first
   argument applied to it gives bounded constructibility of the output. This proves the
   second conclusion.
-/
theorem general_admissibility (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : Scheme.PurityAffineChartCover f)
    (cU : (v : Fin C.baseCount) → Fin (C.chartCount v) → ℕ)
    (hC : C.openComplementConditions P.Coefficient cU)
    (a b : ℤ) (hab : a ≤ b) :
    (∀ K, Scheme.finiteTorsionConstructibleIn P.coefficients.l P.extension P.level
      P.level_pos Y
      (P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k))) a b hab K →
      Scheme.finiteTorsionConstructibleIn P.coefficients.l P.extension P.level
        P.level_pos X (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)))
        (a - 2 * (C.maxEmbeddingDimension : ℤ))
        (b - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ))
        (le_trans (sub_le_sub_right hab _)
          (le_add_of_nonneg_right (Nat.cast_nonneg _)))
        ((P.exceptionalInverseImage f).obj K)) ∧
    (∀ K, finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      Scheme.HasProEtaleTorAmplitude Y P.Ring K a b →
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
        ((P.exceptionalInverseImage f).obj K) ∧
      Scheme.HasProEtaleTorAmplitude X P.Ring ((P.exceptionalInverseImage f).obj K)
        (a - 2 * (C.maxEmbeddingDimension : ℤ))
        (b - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ))) := by
  classical
  let : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  let J := (v : Fin C.baseCount) × Fin (C.chartCount v)
  let U : J → X.Opens := fun t ↦ C.chartOpen t.1 t.2
  have hcover : ∀ x : X, ∃ t : J, x ∈ U t := by
    intro x
    obtain ⟨v, hv⟩ := C.base_cover (f x)
    obtain ⟨i, hi⟩ := C.chart_cover v x hv
    exact ⟨⟨v, i⟩, hi⟩
  let r := a - 2 * (C.maxEmbeddingDimension : ℤ)
  let s := b - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ)
  have hrs : r ≤ s := le_trans (sub_le_sub_right hab _)
    (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hcoh (p q : ℤ) (hpq : p ≤ q) (K : Scheme.proEtaleDerivedCategory Y P.Ring)
      (hK : constructibleInterval P.coefficients.l P.extension P.level P.level_pos Y p q K) :
      constructibleInterval P.coefficients.l P.extension P.level P.level_pos X
        (p - 2 * (C.maxEmbeddingDimension : ℤ))
        (q - 2 * (C.maxEmbeddingDimension : ℤ) + (C.preservationConstant cU : ℤ))
        ((P.exceptionalInverseImage f).obj K) := by
    apply (purityFiniteOpenIntervalDescent P X J U hcover
      ((P.exceptionalInverseImage f).obj K)).1 _ _
      (le_trans (sub_le_sub_right hpq _) (le_add_of_nonneg_right (Nat.cast_nonneg _)))
    intro t
    have ht := (chart_local_bounds P f C t.1 t.2 (cU t.1 t.2)
      (hC t.1 t.2) p q hpq).1 K hK
    have hb := chart_interval_bounds C cU t.1 t.2 p q
    exact ⟨ht.1, fun z hz ↦ ⟨le_trans hb.1 (ht.2 hz).1, le_trans (ht.2 hz).2 hb.2⟩⟩
  constructor
  · intro K hK
    apply (interval_iff P X _ r s hrs _).mpr
    exact hcoh a b hab K ((interval_iff P Y _ a b hab K).mp hK)
  · intro K hK hTor
    have ht : Scheme.HasProEtaleTorAmplitude X P.Ring
        ((P.exceptionalInverseImage f).obj K) r s := by
      apply tor_open_descent P.Ring U hcover _ r s hrs
      intro t
      have hlocal := (chart_local_bounds P f C t.1 t.2 (cU t.1 t.2)
        (hC t.1 t.2) a b hab).2 K hK hTor
      have hb := chart_interval_bounds C cU t.1 t.2 a b
      exact tor_mono hlocal hb.1 hb.2
    refine ⟨⟨?_, r, s, ht⟩, ht⟩
    obtain ⟨p, hp⟩ := hK.1.1.bddBelow
    obtain ⟨q, hq⟩ := hK.1.1.bddAbove
    apply (hcoh (min p q) q (min_le_right _ _) K ?_).1
    refine ⟨hK.1, ?_⟩
    intro z hz
    exact ⟨le_trans (min_le_left _ _) (hp hz), hq hz⟩

end WeilConjectures.PurityFiniteSetting
