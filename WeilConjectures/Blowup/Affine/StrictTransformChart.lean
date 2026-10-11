/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.Algebra.Module.Torsion

/-!

# The strict transform on an affine blow-up chart

Let `A → B` be a ring map, `I ⊆ A` an ideal and `a ∈ I`. The affine chart of the base change
`Spec B ×_{Spec A} Bl_I(Spec A)` at `a` has coordinate ring
`C_a(A, B, I) = B ⊗_A A[I/a]`, and the strict transform of `Spec B` is cut out in it by the
`a`-power torsion: its coordinate ring is `C_a^st(A, B, I) = C_a(A, B, I) / Γ_(a)`. We show that
`C_a^st(A, B, I)` is the chart ring `B[IB/b]` of the blow-up of `Spec B` along `IB`, where `b` is
the image of `a`: the map `σ_a : C_a(A, B, I) → B[IB/b]`, `y ⊗ x/a ↦ y·x̄/b`, is surjective with
kernel the `a`-power torsion.

## Main definitions

- `AlgebraicGeometry.AffineBlowup.BaseChangeChart`: the ring `C_a(A, B, I) = B ⊗_A A[I/a]`.
- `AlgebraicGeometry.AffineBlowup.StrictChart`: the ring `C_a^st(A, B, I) = C_a(A, B, I)/Γ_(a)`.
- `AlgebraicGeometry.AffineBlowup.strictChartMap`: the map `σ_a : C_a(A, B, I) → B[IB/b]`.
- `AlgebraicGeometry.AffineBlowup.strictChartEquiv`: the induced isomorphism
  `σ̄_a : C_a^st(A, B, I) ≃ B[IB/b]`.

## Main results

- `AlgebraicGeometry.AffineBlowup.strictChartMap_surjective`: `σ_a` is surjective.
- `AlgebraicGeometry.AffineBlowup.ker_strictChartMap`: the kernel of `σ_a` is the `a`-power
  torsion of `C_a(A, B, I)`.

-/

@[expose] public section

universe u

open TensorProduct

namespace AlgebraicGeometry.AffineBlowup

variable {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (a : A)

/-- The coordinate ring `C_a(A, B, I) = B ⊗_A A[I/a]` of the chart at `a` of the base change of
the blow-up of `Spec A` along `I` to `Spec B`.
(blueprint: `def-nagata-strict-transform-basechange-chart-ring`) -/
abbrev BaseChangeChart : Type u :=
  B ⊗[A] chartRing I a

/-- The `a`-power torsion `Γ_(a)(C_a(A, B, I))`, an ideal of `C_a(A, B, I)`. -/
abbrev baseChangeChartTorsion : Ideal (BaseChangeChart B I a) :=
  Submodule.powTorsion (BaseChangeChart B I a) (BaseChangeChart B I a)
    (algebraMap A (BaseChangeChart B I a) a)

/-- The coordinate ring `C_a^st(A, B, I) = C_a(A, B, I) / Γ_(a)(C_a(A, B, I))` of the chart at
`a` of the strict transform of `Spec B` in the blow-up of `Spec A` along `I`.
(blueprint: `def-nagata-strict-transform-chart-ring`) -/
abbrev StrictChart : Type u :=
  BaseChangeChart B I a ⧸ baseChangeChartTorsion B I a

/-- The localization map `A_a → B_b` along `A → B`, where `b` is the image of `a`, as a map of
`A`-algebras. -/
noncomputable def awayBaseChange :
    Localization.Away a →ₐ[A] Localization.Away (algebraMap A B a) where
  __ := Localization.awayMap (algebraMap A B) a
  commutes' r := by
    simp [IsLocalization.Away.map, IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]

lemma awayBaseChange_chartFraction (n : ℕ) (x : A) :
    awayBaseChange B a (chartFraction a n x) = chartFraction (algebraMap A B a) n
      (algebraMap A B x) := by
  simp only [chartFraction, Localization.mk_eq_mk']
  change IsLocalization.Away.map _ _ (algebraMap A B) a _ = _
  rw [IsLocalization.Away.map, IsLocalization.map_mk']
  rfl

/-- The map `C_a(A, B, I) → B_b`, `y ⊗ c ↦ y · c̄`, where `b` is the image of `a`. -/
noncomputable def baseChangeChartToAway :
    BaseChangeChart B I a →ₐ[B] Localization.Away (algebraMap A B a) :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) ((awayBaseChange B a).comp (chartRing I a).val)
    fun _ _ ↦ Commute.all _ _

@[simp]
lemma baseChangeChartToAway_tmul (y : B) (c : chartRing I a) :
    baseChangeChartToAway B I a (y ⊗ₜ c) =
      algebraMap B _ y * awayBaseChange B a (c : Localization.Away a) :=
  rfl

lemma baseChangeChartToAway_algebraMap (r : A) :
    baseChangeChartToAway B I a (algebraMap A _ r) = algebraMap A _ r :=
  (baseChangeChartToAway B I a).commutes' _ |>.trans (by simp [← IsScalarTower.algebraMap_apply])

variable {a}

section

variable (ha : a ∈ I)
include ha

/-- Every element of `C_a(A, B, I)` becomes an element of `B` after multiplication by a power of
`a`. -/
lemma exists_pow_mul_eq_algebraMap (z : BaseChangeChart B I a) :
    ∃ (N : ℕ) (w : B), algebraMap A _ a ^ N * z = algebraMap B _ w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul y c =>
    obtain ⟨n, x, hx, hc⟩ := (mem_chartRing_iff I ha).mp c.2
    refine ⟨n, y * algebraMap A B x, ?_⟩
    have hc' : (algebraMap A (chartRing I a) a) ^ n * c = algebraMap A _ x := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, hc]
      rw [← chartFraction_zero, ← map_pow, ← chartFraction_zero, ← chartFraction_mul,
        chartFraction_eq_iff]
      exact ⟨0, by ring⟩
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, hc', Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, mul_comm]
    rfl
  | add z z' hz hz' =>
    obtain ⟨N, w, hw⟩ := hz
    obtain ⟨N', w', hw'⟩ := hz'
    refine ⟨N + N', algebraMap A B a ^ N' * w + algebraMap A B a ^ N * w', ?_⟩
    rw [mul_add, pow_add, mul_right_comm, hw, mul_assoc, hw', map_add, map_mul, map_mul,
      map_pow, map_pow, ← IsScalarTower.algebraMap_apply]
    ring

end

variable (a) in
/-- The image of `C_a(A, B, I)` in `B_b` lies in the chart ring `B[IB/b]`. -/
lemma baseChangeChartToAway_mem_chartRing (ha : a ∈ I) (z : BaseChangeChart B I a) :
    baseChangeChartToAway B I a z ∈ chartRing (I.map (algebraMap A B)) (algebraMap A B a) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y c =>
    rw [baseChangeChartToAway_tmul]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ y) ?_
    obtain ⟨n, x, hx, hc⟩ := (mem_chartRing_iff I ha).mp c.2
    rw [hc, awayBaseChange_chartFraction]
    refine chartFraction_mem_chartRing _ ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  | add z z' hz hz' => rw [map_add]; exact Subalgebra.add_mem _ hz hz'

variable (a) in
/-- The map `σ_a : C_a(A, B, I) → B[IB/b]`, `y ⊗ x/a ↦ y·x̄/b`, where `b` is the image of `a` in
`B`. It is a well-defined homomorphism of `B`-algebras by the universal properties of
`A[I/a] ⊆ A_a` and of the tensor product.
(blueprint: `def-nagata-strict-chart-to-extended-blowup-chart`,
`lemma-nagata-strict-chart-to-extended-blowup-chart`) -/
noncomputable def strictChartMap (ha : a ∈ I) :
    BaseChangeChart B I a →ₐ[B] chartRing (I.map (algebraMap A B)) (algebraMap A B a) :=
  (baseChangeChartToAway B I a).codRestrict _ (baseChangeChartToAway_mem_chartRing B I a ha)

/-- The defining formula of `σ_a` on pure tensors of chart generators: `σ_a(y ⊗ x/a) = y·x̄/b`.
(blueprint: `def-nagata-strict-chart-to-extended-blowup-chart`) -/
lemma coe_strictChartMap_tmul (ha : a ∈ I) (y : B) (x : A) (hx : chartFraction a 1 x ∈ chartRing I a) :
    (strictChartMap B I a ha (y ⊗ₜ ⟨chartFraction a 1 x, hx⟩) :
      Localization.Away (algebraMap A B a)) =
      algebraMap B _ y * chartFraction (algebraMap A B a) 1 (algebraMap A B x) := by
  change baseChangeChartToAway B I a _ = _
  rw [baseChangeChartToAway_tmul, awayBaseChange_chartFraction]

lemma coe_strictChartMap (ha : a ∈ I) (z : BaseChangeChart B I a) :
    (strictChartMap B I a ha z : Localization.Away (algebraMap A B a)) =
      baseChangeChartToAway B I a z :=
  rfl

/-- **`σ_a` is surjective**: the chart ring `B[IB/b]` is generated over `B` by the fractions
`ȳ/b`, `y ∈ IB`, all of which lie in the image of `σ_a`.
(blueprint: `lemma-nagata-strict-chart-map-surjective`) -/
theorem strictChartMap_surjective (ha : a ∈ I) :
    Function.Surjective (strictChartMap B I a ha) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  rintro ⟨z, hz⟩ -
  -- the image of `σ_a` in `B_b`
  set R : Subalgebra B (Localization.Away (algebraMap A B a)) :=
    (baseChangeChartToAway B I a).range with hR
  suffices hzR : z ∈ R by
    obtain ⟨w, hw⟩ := hzR
    exact ⟨w, Subtype.ext hw⟩
  refine (Algebra.adjoin_le ?_ : chartRing (I.map (algebraMap A B)) (algebraMap A B a) ≤ R) hz
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  simp only
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hx1 : x ∈ I ^ 1 := by rwa [pow_one]
    refine ⟨1 ⊗ₜ ⟨chartFraction a 1 x, chartFraction_mem_chartRing I hx1⟩, ?_⟩
    rw [baseChangeChartToAway_tmul, map_one, one_mul]
    exact awayBaseChange_chartFraction B a 1 x
  | zero =>
    rw [← map_zero (algebraMap B (Localization.Away (algebraMap A B a))), ← chartFraction_zero,
      chartFraction_eq_iff.mpr ⟨0, by simp⟩]
    exact zero_mem R
  | add y y' _ _ hy hy' =>
    rw [chartFraction_add]
    exact add_mem hy hy'
  | smul c y _ hy =>
    have : chartFraction (algebraMap A B a) 1 (c • y) =
        algebraMap B _ c * chartFraction (algebraMap A B a) 1 y := by
      rw [← chartFraction_zero, smul_eq_mul, ← chartFraction_mul, zero_add]
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem R c) hy

/-- **The kernel of `σ_a` is the `a`-power torsion** of `C_a(A, B, I)`: an element killed by
`σ_a` becomes an element `w ∈ B` after multiplication by a power of `a`, and `w/1 = 0` in `B_b`
means that `w` is killed by a power of `b`.
(blueprint: `lemma-nagata-strict-chart-map-kernel`) -/
theorem ker_strictChartMap (ha : a ∈ I) :
    RingHom.ker (strictChartMap B I a ha) = baseChangeChartTorsion B I a := by
  ext z
  rw [RingHom.mem_ker, Submodule.mem_powTorsion_iff, ← Subtype.coe_inj, coe_strictChartMap,
    ZeroMemClass.coe_zero]
  have hσ : ∀ z : BaseChangeChart B I a, ∀ n : ℕ,
      baseChangeChartToAway B I a (algebraMap A _ a ^ n * z) =
        algebraMap B _ (algebraMap A B a) ^ n * baseChangeChartToAway B I a z := by
    intro z n
    rw [map_mul, map_pow, baseChangeChartToAway_algebraMap, IsScalarTower.algebraMap_apply A B]
  constructor
  · intro hz
    obtain ⟨N, w, hw⟩ := exists_pow_mul_eq_algebraMap B I ha z
    have h1 := hσ z N
    rw [hz, mul_zero, hw, AlgHom.commutes] at h1
    obtain ⟨⟨_, M, rfl⟩, hM⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers _) _ _).mp h1
    refine ⟨M + N, ?_⟩
    rw [smul_eq_mul, pow_add, mul_assoc, hw, ← map_pow, ← map_mul,
      IsScalarTower.algebraMap_apply A B, ← map_pow, ← map_mul, hM, map_zero]
  · rintro ⟨n, hn⟩
    have h1 := hσ z n
    rw [← smul_eq_mul, hn, map_zero] at h1
    have hu : IsUnit (algebraMap B (Localization.Away (algebraMap A B a)) (algebraMap A B a) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit _).pow n
    exact (hu.mul_right_eq_zero).mp h1.symm

/-- The comparison `σ̄_a : C_a^st(A, B, I) → B[IB/b]` induced by `σ_a` on the quotient by the
`a`-power torsion. (blueprint: `def-nagata-strict-transform-chart-comparison`) -/
noncomputable def strictChartComparison (ha : a ∈ I) :
    StrictChart B I a →ₐ[B] chartRing (I.map (algebraMap A B)) (algebraMap A B a) :=
  Ideal.Quotient.liftₐ _ (strictChartMap B I a ha) fun z hz ↦ by
    rw [← RingHom.mem_ker, ← ker_strictChartMap B I ha] at *
    exact hz

@[simp]
lemma strictChartComparison_mk (ha : a ∈ I) (z : BaseChangeChart B I a) :
    strictChartComparison B I ha (Ideal.Quotient.mk _ z) = strictChartMap B I a ha z :=
  rfl

/-- **The strict-transform chart comparison is a ring isomorphism**
`σ̄_a : C_a^st(A, B, I) ≃ B[IB/b]`: `σ_a` is surjective and its kernel is exactly the ideal
by which `C_a(A, B, I)` is divided. (blueprint: `prop-nagata-strict-transform-chart-iso`) -/
theorem strictChartComparison_bijective (ha : a ∈ I) :
    Function.Bijective (strictChartComparison B I ha) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [strictChartComparison_mk, ← RingHom.mem_ker, ker_strictChartMap] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro w
    obtain ⟨z, rfl⟩ := strictChartMap_surjective B I ha w
    exact ⟨_, strictChartComparison_mk B I ha z⟩

/-- The strict-transform chart comparison `σ̄_a` as an isomorphism of `B`-algebras
`C_a^st(A, B, I) ≃ B[IB/b]`. (blueprint: `prop-nagata-strict-transform-chart-iso`) -/
noncomputable def strictChartEquiv (ha : a ∈ I) :
    StrictChart B I a ≃ₐ[B] chartRing (I.map (algebraMap A B)) (algebraMap A B a) :=
  AlgEquiv.ofBijective (strictChartComparison B I ha) (strictChartComparison_bijective B I ha)

@[simp]
lemma strictChartEquiv_apply (ha : a ∈ I) (z : StrictChart B I a) :
    strictChartEquiv B I ha z = strictChartComparison B I ha z :=
  rfl

end AlgebraicGeometry.AffineBlowup
