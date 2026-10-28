/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
import Sheaf.DeligneLaumon.PairEigenvalueCurveTest

/-! # Purity of constituents on a smooth affine base

The constituent step of the arbitrary-base real-sheaf argument, stated for the
source library's constructible pro-étale Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

private theorem weight_power_normalization {K : Type*} [Field K] (ι : K →+* ℂ)
    (q e : ℕ) (he : 0 < e) (α : K) :
    WeilGroup.frobeniusWeight ι (q ^ e) (α ^ e) =
      WeilGroup.frobeniusWeight ι q α := by
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
  simp only [WeilGroup.frobeniusWeight, map_pow, norm_pow, Nat.cast_pow, Real.log_pow]
  rw [mul_left_comm (2 : ℝ) (e : ℝ), mul_div_mul_left _ _ he']

/-- An irreducible lisse subquotient of a real lisse sheaf on a smooth affine
finite-type scheme over a finite field is punctually pure.

Source: Deligne, Weil II, §1.8; current blueprint
`sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
paragraphs 1--5 and the dimension-zero case in paragraph 7.
(blueprint: lem-zl-smooth-affine-constituent-purity).

Proof: A simple lisse Weil object is supported on a single connected component:
the decomposition into the finitely many open-and-closed components is a
decomposition by Weil subobjects. After a finite constant extension, split its
geometric components and its geometric constituents using the geometric socle
and Frobenius permutation argument of geometric-constituents-any-base. The
resulting filtration is an actual filtration of lisse Weil sheaves; inverse
image is exact and carries the given subquotient of the real sheaf to that
filtration. Reality survives because every new local Frobenius is a positive
power of the original operator. On a positive-dimensional geometric component,
fix an anchor closed point and join it to any other closed point by a curve
preserving the geometric irreducibility of every constituent. The curve purity
theorem makes these subquotients pure there. At the anchor, raising eigenvalues
and residue cardinalities to the same positive power fixes each weight as
2 log_q |iota(alpha)|, independent of the curve. The same calculation at the
other point proves purity everywhere. Frobenius permutes the geometric
constituents transitively, since a proper union of its orbits would give a
proper Weil subobject of the original simple object. Their weights agree:
Frobenius transport conjugates the local operators and preserves residue
cardinalities. Thus every quotient in the pulled-back simple object has this
same weight. Exactness of stalks shows that the whole pulled-back object is
pure of that weight, even for a nonsplit filtration. The residue-power
calculation descends this purity to the original object. In dimension zero,
the connected component is the spectrum of a finite field. Its simple Weil
object is an eigenline of its invertible Frobenius, of weight
2 log_q |iota(alpha)|. Off its support the stalk is zero, so purity is vacuous.
An empty base has no simple lisse object and hence cannot satisfy the
irreducibility hypothesis. -/
theorem IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth_affine
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsAffine X]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l X}
    (hG : G.IsLisse) (hreal : G.IsReal ι) {G₁ G₂ : WeilSheaf k₀ l X}
    (i : G₁ ⟶ G₂) (j : G₂ ⟶ G) [Mono i] [Mono j]
    (h₁ : G₁.IsLisse) (h₂ : G₂.IsLisse)
    (hirr : (cokernel i).IsIrreducibleLisse) :
    ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w := by
  obtain ⟨x, hx⟩ := (cokernel i).exists_nontrivial_stalk_of_not_isZero hirr.2.1
  have := hx
  obtain ⟨α, hα⟩ := ((cokernel i).stalk x).frobeniusEnd.exists_eigenvalue
  refine ⟨WeilGroup.frobeniusWeight ι
    ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) α, ?_⟩
  intro y β hβ
  obtain ⟨k₁, _, _, _, _, C, _, _, _, _, _, _, _, H, H₁, H₂, a, b,
      _, _, hH, hH₁, hH₂, hsimple, hrealH, s, t, e, f, he, hf,
      hs, ht, hαs, hβt, _⟩ :=
    exists_pair_eigenvalue_curve_test hG i j h₁ h₂ hirr x y α β hα hβ
  obtain ⟨w, hw⟩ := (hrealH ι hreal).exists_isPunctuallyPureOfWeight_cokernel
    hH a b hH₁ hH₂ hsimple
  have hsq : 1 < (C ↘ Spec (CommRingCat.of k₁)).residueCard s.1 := by
    have hnorm : (C ↘ Spec (CommRingCat.of k₁)).residueCard s.1 =
        C.pointNorm s.1 := (Scheme.Hom.pointNorm_eq_pow_degreeOver _ s.2).symm
    rw [hnorm]
    exact C.one_lt_pointNorm s.2
  have htq : 1 < (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 := by
    have hnorm : (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 =
        C.pointNorm t.1 := (Scheme.Hom.pointNorm_eq_pow_degreeOver _ t.2).symm
    rw [hnorm]
    exact C.one_lt_pointNorm t.2
  have has := (WeilGroup.isOfWeight_iff_frobeniusWeight_eq hsq
    (FrobeniusModule.ne_zero_of_hasEigenvalue hαs)).mp (hw s _ hαs)
  have hbt := (WeilGroup.isOfWeight_iff_frobeniusWeight_eq htq
    (FrobeniusModule.ne_zero_of_hasEigenvalue hβt)).mp (hw t _ hβt)
  rw [hs, weight_power_normalization ι _ _ he] at has
  rw [ht, weight_power_normalization ι _ _ hf] at hbt
  have hyq : 1 < (X ↘ Spec (CommRingCat.of k₀)).residueCard y.1 := by
    have hnorm : (X ↘ Spec (CommRingCat.of k₀)).residueCard y.1 =
        X.pointNorm y.1 := (Scheme.Hom.pointNorm_eq_pow_degreeOver _ y.2).symm
    rw [hnorm]
    exact X.one_lt_pointNorm y.2
  exact (WeilGroup.isOfWeight_iff_frobeniusWeight_eq hyq
    (FrobeniusModule.ne_zero_of_hasEigenvalue hβ)).mpr (hbt.trans has.symm)

end AlgebraicGeometry.WeilSheaf
