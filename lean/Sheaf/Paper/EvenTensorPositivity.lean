/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Logic.Function.Iterate
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.Tensor
import WeilConjectures.WeilSheaf.StalkTensor
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Real
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Sheaf.Paper.AdicLocalCharacteristicFactor

/-!
# Reality and positivity of tensor powers of a real Weil sheaf

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-p-real-rankin, lem-rp-even-tensor-positivity
(blueprint: lem-rp-even-tensor-positivity).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped ComplexOrder

namespace AlgebraicGeometry.WeilSheaf

/-- Every positive tensor power of a lisse real Weil sheaf has real local polynomials;
for even powers their inverse local factors have nonnegative real coefficients and constant
term one. Source: blueprint main-20261015, sk-p-real-rankin,
lem-rp-even-tensor-positivity (blueprint: lem-rp-even-tensor-positivity).

The `k`-fold tensor power for `k ≥ 1` is written by iterating `G.tensorObj` exactly `k - 1`
times starting with `G`. This uses the tensor over the continuous coefficient sheaf, with
its canonical tensor Weil structure, rather than tensor over the discrete coefficient ring.
The complex order means both that each coefficient is real and that its real part is
nonnegative.

Proof: Fix a closed point and let `zᵢ` be its complex Frobenius eigenvalues. Reality of `G`
means that conjugation permutes this multiset (def-wf-iota-real). Iterating the tensor-spectrum
formula (p-linear-spectra), using the tensor action of def-real-weil-representation-operations,
gives the products `zᵢ₁ ... zᵢₖ` as the eigenvalues of the tensor stalk. Conjugation permutes
these products, so their characteristic factor has real coefficients and constant term one.
Apply the coefficient embedding entrywise to Frobenius matrices; it commutes with tensor
products and determinants. Triangularize over the algebraically closed field of complex
numbers (p-linear-triangular). Powers of these triangular matrices have the powers of their
diagonal entries on the diagonal, so the trace of the n-th power on the tensor stalk is
`(∑ i, zᵢ ^ n) ^ k`. The sum is real by conjugation invariance, and its even powers are
nonnegative. The formal trace-determinant identity (lem-weil-exp-trace-determinant) identifies
the inverse local factor with the exponential of the series whose n-th positive coefficient
is this trace divided by n. These coefficients are nonnegative when k is even. The finite
coefficient formula for the formal exponential (def-weil-power-series-exponential) expresses
every positive coefficient as a finite sum of products of these nonnegative numbers, divided
by positive factorials. Its constant coefficient is one. For a zero stalk the determinant
is the empty product one and the same formulas apply. -/
theorem isReal_tensorPower_and_even_nonneg
    {l : ℕ} [Fact l.Prime]
    {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (ι : PadicAlgCl l ≃+* ℂ) (G : WeilSheaf k₀ l X) (hG : G.IsLisse)
    (hreal : G.IsReal ι.toRingHom) (x : X.finitePoints) (k : ℕ) (hk : 1 ≤ k) :
    ((Nat.iterate (fun H => G.tensorObj H hG) (k - 1) G).stalk x).IsReal ι.toRingHom ∧
      (Even k →
        (∀ n : ℕ, 0 ≤ PowerSeries.coeff n
          (((Polynomial.map ι.toRingHom
            ((Nat.iterate (fun H => G.tensorObj H hG) (k - 1) G).stalk x).localPolynomial :
              Polynomial ℂ) : PowerSeries ℂ)⁻¹)) ∧
        PowerSeries.constantCoeff
          (((Polynomial.map ι.toRingHom
            ((Nat.iterate (fun H => G.tensorObj H hG) (k - 1) G).stalk x).localPolynomial :
              Polynomial ℂ) : PowerSeries ℂ)⁻¹) = 1) := by
  classical
  have htrace (j : ℕ) : ∀ k : ℕ, 1 ≤ k →
      LinearMap.trace (PadicAlgCl l) _
        (((Nat.iterate (fun H ↦ G.tensorObj H hG) (k - 1) G).stalk x).frobeniusEnd ^ j) =
      LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ j) ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have he := (stalkTensorObjEquiv G
        (Nat.iterate (fun H ↦ G.tensorObj H hG) (k - 1) G) hG x).trace_frobeniusEnd_pow j
      change LinearMap.trace (PadicAlgCl l) _
        ((TensorProduct.map (G.stalk x).frobeniusEnd
          ((Nat.iterate (fun H ↦ G.tensorObj H hG) (k - 1) G).stalk x).frobeniusEnd) ^ j) =
        _ at he
      rw [TensorProduct.map_pow, LinearMap.trace_tensorProduct'] at he
      rw [show k + 1 - 1 = (k - 1) + 1 by omega,
        Function.iterate_succ_apply', ← he, ih, pow_succ']
  have htrreal (j : ℕ) :
      starRingEnd ℂ (ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ j))) =
        ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ j)) :=
    (FrobeniusModule.isReal_iff_forall_trace_pow ι.toRingHom (G.stalk x)).1 (hreal x) j
  let M := (Nat.iterate (fun H ↦ G.tensorObj H hG) (k - 1) G).stalk x
  have hMreal : M.IsReal ι.toRingHom := by
    rw [FrobeniusModule.isReal_iff_forall_trace_pow]
    intro j
    change starRingEnd ℂ (ι (LinearMap.trace (PadicAlgCl l) _ (M.frobeniusEnd ^ j))) =
      ι (LinearMap.trace (PadicAlgCl l) _ (M.frobeniusEnd ^ j))
    rw [htrace j k hk, map_pow, map_pow, htrreal]
  refine ⟨hMreal, fun heven ↦ ⟨?_, ?_⟩⟩
  · let s := M.frobeniusEnd.charpoly.roots.map ι.toRingHom
    have hsum (j : ℕ) : (s.map (· ^ j)).sum =
        ι (LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ j)) ^ k := by
      rw [← map_pow, ← htrace j k hk, LinearMap.trace_pow_eq_sum_pow_roots_charpoly,
        map_multiset_sum]
      simp only [s, Multiset.map_map, map_pow, Function.comp_def]
      rfl
    have hpos (j : ℕ) : 0 ≤ (s.map (· ^ j)).sum := by
      rw [hsum, ← Complex.conj_eq_iff_re.1 (htrreal j), ← Complex.ofReal_pow]
      exact Complex.zero_le_real.2 (heven.pow_nonneg _)
    have hpoly : (((Polynomial.map ι.toRingHom M.localPolynomial : Polynomial ℂ) :
        PowerSeries ℂ)) = (s.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod := by
      rw [FrobeniusModule.localPolynomial, LinearMap.charpolyRev_eq_prod_roots,
        Polynomial.map_multiset_prod, Multiset.map_map,
        ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
      simp [s, Multiset.map_map]
    change ∀ n, 0 ≤ PowerSeries.coeff n
      (((Polynomial.map ι.toRingHom M.localPolynomial : Polynomial ℂ) : PowerSeries ℂ)⁻¹)
    rw [hpoly]
    exact PowerSeries.coeff_inv_prod_one_sub_C_mul_X_nonneg s (fun j _ ↦ hpos j)
  · change PowerSeries.constantCoeff
      (((Polynomial.map ι.toRingHom M.localPolynomial : Polynomial ℂ) : PowerSeries ℂ)⁻¹) = 1
    rw [PowerSeries.constantCoeff_inv, Polynomial.constantCoeff_coe, Polynomial.coeff_map]
    simp [FrobeniusModule.localPolynomial, LinearMap.coeff_zero_charpolyRev]

end AlgebraicGeometry.WeilSheaf
