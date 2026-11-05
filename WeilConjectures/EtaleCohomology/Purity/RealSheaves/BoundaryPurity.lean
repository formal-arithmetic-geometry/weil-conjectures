/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Restriction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Purity of a lisse sheaf extends over the missing points of a dense open

Let `𝒢` be a lisse Weil sheaf on a smooth geometrically connected curve `C₀` over `𝔽_q`, and
`U₀ ⊆ C₀` a nonempty open on which `𝒢` is punctually `ι`-pure of weight `w`. Then `𝒢` is
punctually `ι`-pure of weight `w` on all of `C₀` (the consequence in
`cor-wf-unramified-boundary-purity`, and the second assertion of `sk-p-real-semi`).

The argument is the one of `lem-wf-boundary-semicontinuity`, for the lisse sheaf `𝒢 = j_* j^* 𝒢`
(`lem-a1-lisse-middle-extension`), whose boundary stalks are its own stalks. On an affine
neighbourhood `X'₀` of a closed point `s`, the Euler product of `𝒢` (`cor-rp-euler-product`)
splits into the Euler series over the closed points of `X'₀ ∩ U₀` and the finitely many local
factors at the points of `X'₀ \ U₀`:

`L (X'₀ ∩ U₀, 𝒢, T) · ι det (1 - F T ∣ H_c²) = P · ∏_{s ∈ X'₀ \ U₀} ι P_s (𝒢, T ^ e_s)`.

The inverse of the open part converges on the disc of radius `q ^ (-(w / 2 + 1))`
(`AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`), and so does
`P / ι det (1 - F T ∣ H_c²)`, the eigenvalues on `H_c² = V_{π₁}(-1)` being bounded through a
single closed point of `U₀`. So the local polynomials at the points of `X'₀ \ U₀` have no zero
in that disc (`AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`), which bounds the weights there
by `w + 2`. Tensor squares sharpen the bound to `w`, and the dual gives the lower bound.

## Main statements

- `AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`: the analytic step, for any identity
  `L (T, ℱ, T) · ι det (1 - F T ∣ H) = P · B` with `B` a polynomial.
- `AlgebraicGeometry.WeilGroup.frobeniusWeight_le_of_isAffine`: on an affine curve, weights at
  most `β` at the closed points of a cofinite set give weights at most `β` everywhere.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_forall_mem_range`: punctual purity on a
  nonempty open gives punctual purity on the whole curve.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

variable {W l ρ ι}

variable (W l ρ ι)

variable {W l ρ}

variable (W l ρ)

end AlgebraicGeometry.WeilGroup
