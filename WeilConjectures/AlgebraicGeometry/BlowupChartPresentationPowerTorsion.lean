/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Blowup.Affine.ChartAlgebra

/-!
# The power-torsion kernel of a blowup chart presentation

Source: Stacks Project, Algebra, Tag 0G8S, lemma-affine-blowup-quotient-description
(blueprint: lem-trf-blowup-chart-presentation-power-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Polynomial induction clears the denominators imposed by the relations `b * X i = c i`.
Constants use exponent zero, sums add the two exponents, and multiplication by a variable
increases the exponent by one. This is the constant-multiple calculation in the direct proof
of Stacks Project, Algebra, Tag 0G8S.
(blueprint: lem-trf-blowup-chart-presentation-power-torsion) -/
private theorem presentation_constant_multiple
    {R Q : Type u} {σ : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (f : MvPolynomial σ R →ₐ[R] Q) (b : R) (c : σ → R)
    (hX : ∀ i, algebraMap R Q b * f (MvPolynomial.X i) = algebraMap R Q (c i))
    (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (r : R), algebraMap R Q b ^ n * f p = algebraMap R Q r := by
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨0, r, by simp⟩
  | add p q hp hq =>
    obtain ⟨n, r, hr⟩ := hp
    obtain ⟨m, t, ht⟩ := hq
    refine ⟨n + m, b ^ m * r + b ^ n * t, ?_⟩
    calc
      _ = algebraMap R Q b ^ m * (algebraMap R Q b ^ n * f p) +
          algebraMap R Q b ^ n * (algebraMap R Q b ^ m * f q) := by
        rw [map_add, pow_add]
        ring
      _ = _ := by rw [hr, ht]; simp only [map_add, map_mul, map_pow]
  | mul_X p i hp =>
    obtain ⟨n, r, hr⟩ := hp
    refine ⟨n + 1, r * c i, ?_⟩
    calc
      _ = (algebraMap R Q b ^ n * f p) *
          (algebraMap R Q b * f (MvPolynomial.X i)) := by
        rw [map_mul, pow_succ]
        ring
      _ = _ := by rw [hr, hX, map_mul]

/-- The assignments `y_i ↦ a_i/a` induce a surjective algebra homomorphism from the
polynomial quotient to the affine blowup chart. Its kernel consists exactly of the
classes killed by some nonnegative power of `a`. No regularity is assumed.
Here `s` counts the generators other than `a 0`, so `s = 0` includes the one-generator case.

Source: Stacks Project, Algebra, Tag 0G8S, lemma-affine-blowup-quotient-description.
(blueprint: lem-trf-blowup-chart-presentation-power-torsion)

Proof (the node's direct finite-support argument):
1. Use the evaluation map of `def-weil-pbc-mv-polynomial-ring` into the localization
   of `def-weil-ring-localization-away`, sending `y_i` to `a_i/a`. These fractions
   belong to `chartRing` of `def-nagata-blowup-chart-ring`. The relations `a*y_i-a_i`
   evaluate to zero, so `def-weil-pbc-algebra-hom-quotient` descends evaluation to the
   displayed quotient, preserving the algebra structure and the generator images.
2. The image contains every `a_i/a` and the constants. Write any element of the
   generator ideal as `r*a + sum r_i*a_i`. Its fraction is then
   `r + sum r_i*(a_i/a)`. Thus the image contains the defining generators of the
   chart subalgebra and evaluation is surjective.
3. Polynomial induction proves that every representative `f` has `a^d*[f] = [b]`
   for some exponent `d` and constant `b`. Constants use exponent zero. For a sum,
   add the two exponents and adjust the constants by the complementary powers.
   Multiplication by `y_i` increases the exponent by one, using `a*[y_i] = [a_i]`.
   Applying the evaluation map gives `b/1 = (a/1)^d*φ([f])`.
4. If `φ([f]) = 0`, then `b/1 = 0`. The defining localization equivalence gives
   `a^k*b = 0` for some `k`, hence `a^(d+k)*[f] = 0`. Conversely, a class killed
   by `a^N` maps to zero because `a/1` is a unit in the localization, and the chart
   subalgebra embeds in that localization. This proves the kernel characterization.
-/
theorem blowupChartPresentationPowerTorsion
    {R : Type u} [CommRing R] (s : ℕ) (a : Fin (s + 1) → R) :
    ∃ φ :
        (MvPolynomial (Fin s) R ⧸
            Ideal.span (Set.range (fun i : Fin s ↦
              MvPolynomial.C (a 0) * MvPolynomial.X i - MvPolynomial.C (a i.succ)))) →ₐ[R]
          AffineBlowup.chartRing (Ideal.span (Set.range a)) (a 0),
      (∀ i : Fin s,
        (φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) : Localization.Away (a 0)) =
          AffineBlowup.chartFraction (a 0) 1 (a i.succ)) ∧
      Function.Surjective φ ∧
      ∀ z, φ z = 0 ↔ ∃ N : ℕ, (algebraMap R _ (a 0)) ^ N * z = 0 := by
  classical
  let I : Ideal R := Ideal.span (Set.range a)
  let B := AffineBlowup.chartRing I (a 0)
  let J : Ideal (MvPolynomial (Fin s) R) := Ideal.span (Set.range (fun i : Fin s ↦
    MvPolynomial.C (a 0) * MvPolynomial.X i - MvPolynomial.C (a i.succ)))
  let Q := MvPolynomial (Fin s) R ⧸ J
  let q : MvPolynomial (Fin s) R →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  let y : Fin s → B := fun i ↦ ⟨AffineBlowup.chartFraction (a 0) 1 (a i.succ),
    Algebra.subset_adjoin ⟨⟨a i.succ, Ideal.subset_span ⟨i.succ, rfl⟩⟩, rfl⟩⟩
  let e : MvPolynomial (Fin s) R →ₐ[R] B := MvPolynomial.aeval y
  have frac_mul (r : R) :
      algebraMap R (Localization.Away (a 0)) (a 0) *
        AffineBlowup.chartFraction (a 0) 1 r = algebraMap R _ r := by
    rw [← AffineBlowup.chartFraction_zero, ← AffineBlowup.chartFraction_mul,
      ← AffineBlowup.chartFraction_zero, AffineBlowup.chartFraction_eq_iff]
    exact ⟨0, by ring⟩
  have erel (i : Fin s) :
      e (MvPolynomial.C (a 0) * MvPolynomial.X i - MvPolynomial.C (a i.succ)) = 0 := by
    apply Subtype.ext
    simpa [e, y, sub_eq_zero] using frac_mul (a i.succ)
  have hJ : ∀ p ∈ J, e p = 0 := by
    change J ≤ RingHom.ker (e : _ →+* B)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact erel i
  let φ : Q →ₐ[R] B := Ideal.Quotient.liftₐ J e hJ
  have φq (p : MvPolynomial (Fin s) R) : φ (q p) = e p :=
    Ideal.Quotient.lift_mk J (e : _ →+* B) hJ
  have φX (i : Fin s) : (φ (q (MvPolynomial.X i)) : Localization.Away (a 0)) =
      AffineBlowup.chartFraction (a 0) 1 (a i.succ) := by
    rw [φq]
    simp [e, y]
  let E : Q →ₐ[R] Localization.Away (a 0) := B.val.comp φ
  have hB : B ≤ E.range := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    change AffineBlowup.chartFraction (a 0) 1 x ∈ E.range
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · have h : AffineBlowup.chartFraction (a 0) 1 (a 0) = 1 := by
          rw [← map_one (algebraMap R (Localization.Away (a 0))),
            ← AffineBlowup.chartFraction_zero, AffineBlowup.chartFraction_eq_iff]
          exact ⟨0, by ring⟩
        rw [h]
        exact E.range.one_mem
      · exact ⟨q (MvPolynomial.X j), φX j⟩
    | zero =>
      have h : AffineBlowup.chartFraction (a 0) 1 (0 : R) = 0 :=
        Localization.mk_zero _
      rw [h]
      exact E.range.zero_mem
    | add x z _ _ hx hz =>
      rw [AffineBlowup.chartFraction_add]
      exact E.range.add_mem hx hz
    | smul r x _ hx =>
      have h : AffineBlowup.chartFraction (a 0) 1 (r • x) =
          algebraMap R _ r * AffineBlowup.chartFraction (a 0) 1 x := by
        rw [← AffineBlowup.chartFraction_zero, smul_eq_mul,
          ← AffineBlowup.chartFraction_mul, zero_add]
      rw [h]
      exact E.range.mul_mem (E.range.algebraMap_mem r) hx
  refine ⟨φ, φX, ?_, ?_⟩
  · intro z
    obtain ⟨w, hw⟩ := hB z.property
    exact ⟨w, Subtype.ext hw⟩
  · intro z
    have qX (i : Fin s) : algebraMap R Q (a 0) * q (MvPolynomial.X i) =
        algebraMap R Q (a i.succ) := by
      change q (MvPolynomial.C (a 0)) * q (MvPolynomial.X i) =
        q (MvPolynomial.C (a i.succ))
      rw [← map_mul, ← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    constructor
    · intro hz
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
      change φ (q p) = 0 at hz
      obtain ⟨n, r, hr⟩ := presentation_constant_multiple q (a 0)
        (fun i : Fin s ↦ a i.succ) qX p
      have he : E (q p) = 0 := by
        change (φ (q p) : Localization.Away (a 0)) = 0
        rw [hz, ZeroMemClass.coe_zero]
      have hr0 : algebraMap R (Localization.Away (a 0)) r = 0 := by
        have h := congrArg E hr
        simpa only [map_mul, map_pow, AlgHom.commutes, he, mul_zero] using h.symm
      obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (a 0)) _ r).mp hr0
      refine ⟨k + n, ?_⟩
      change algebraMap R Q (a 0) ^ (k + n) * q p = 0
      rw [pow_add, mul_assoc, hr, ← map_pow, ← map_mul, hk, map_zero]
    · rintro ⟨n, hn⟩
      apply Subtype.ext
      change E z = 0
      have h := congrArg E hn
      rw [map_mul, map_pow, AlgHom.commutes, map_zero] at h
      exact ((IsLocalization.Away.algebraMap_isUnit (a 0)).pow n).mul_right_eq_zero.mp h

end AlgebraicGeometry
