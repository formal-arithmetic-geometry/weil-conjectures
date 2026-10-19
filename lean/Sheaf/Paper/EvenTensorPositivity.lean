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
import Sheaf.Paper.PbcWeilCategory
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.ZetaLinearAlgebra.DetTrace
import Mathlib.RingTheory.PowerSeries.Exp
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
  sorry

end AlgebraicGeometry.WeilSheaf
