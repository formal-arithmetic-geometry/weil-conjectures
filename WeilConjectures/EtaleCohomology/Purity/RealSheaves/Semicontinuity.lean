/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin
public import WeilConjectures.PointCountBound

/-!
# Semi-continuity of weights at the boundary of an open subcurve

Let `j : U₀ ↪ C₀` be a nonempty open of a smooth geometrically connected curve over `𝔽_q`, with
a boundary datum, and let `ℱ` be a lisse Weil sheaf on `U₀` with punctual weights at most `β`.
This file proves that the middle extension `j_* ℱ` has punctual weights at most `β` at every
boundary point `s`: every eigenvalue `α` of the residue Frobenius `F_s` on the boundary stalk
`V ^ (I_s)` satisfies `|ι α| ^ 2 ≤ q_s ^ β` (`lem-wf-boundary-semicontinuity`).

The argument is analytic. On an affine neighbourhood `X'₀` of `s`, with `U'₀ = U₀ ∩ X'₀`:

* the inverse of the Euler series `L (U'₀, ℱ, T)` has radius of convergence at least
  `R = q ^ (-(β / 2 + 1))`, because the closed points of `U'₀` of degree `e` number at most
  `A q ^ e` (`lem-wf-point-count-linear-growth`), so that the coefficients of the inverse are
  dominated by those of `∏_x (1 + q_x ^ (β / 2) T ^ e_x) ^ r`;
* the eigenvalues of the geometric Frobenius on `H_c² = V_{π₁(U)} (-1)` (`lem-a1-affine-hc2`)
  have absolute value at most `q ^ (β / 2 + 1)`;
* the Euler product identity for `j_* ℱ` (`lem-wf-euler-product-middle-extension`), the
  Grothendieck–Lefschetz trace formula, then forces the boundary polynomials
  `det (1 - F_s T ^ e_s ∣ V ^ (I_s))` to have no zero in the disc `|T| < R`,

which gives `|ι α| ≤ q_s ^ (β / 2 + 1)`. Applying this to the tensor powers `ℱ ^ ⊗ 2 ^ k`, whose
boundary stalks contain `v ^ ⊗ 2 ^ k` for an eigenvector `v`, sharpens the bound to `β`.

## Implementation notes

The cohomology `H_c² (U, ℱ)` of a Weil representation is not available; as in
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin`, the coinvariant Tate twist
`V_{π₁(U)} (-1)` is used in its place (`AlgebraicGeometry.WeilGroup.compactTopFrobenius`).

The Euler-product form of the trace formula for middle extensions is the hypothesis
`AlgebraicGeometry.BoundaryDatum.HasMiddleExtensionEulerProduct` of the main results: the
Grothendieck–Lefschetz trace formula is not available, and the identity is not a consequence of
the fields of a `AlgebraicGeometry.BoundaryDatum`, which pin the inertia groups down only through
the closed normal subgroup they generate (`AlgebraicGeometry.BoundaryDatum.ker_restrict_eq`).

## Main definitions

- `AlgebraicGeometry.BoundaryDatum.boundaryPolynomial`: `ι det (1 - F_s T ^ e_s ∣ V ^ (I_s))`.
- `AlgebraicGeometry.BoundaryDatum.HasMiddleExtensionEulerProduct`: the Euler-product identity
  for middle extensions.

## Main statements

- `AlgebraicGeometry.WeilGroup.norm_le_of_hasEigenvalue_compactTopFrobenius`
- `AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_add_two`
- `AlgebraicGeometry.BoundaryDatum.sq_norm_le_rpow_of_hasEigenvalue_boundaryFrobenius`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_eq_of_isPunctuallyPure`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K]

namespace WeilGroup

variable {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p) (l : ℕ)
  [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
  (ι : PadicAlgCl l →+* ℂ)

section TopCohomology

end TopCohomology

section Radius

open PowerSeries

variable {W l ρ ι}

variable (W l ρ ι)

end Radius

end WeilGroup

namespace BoundaryDatum

variable {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p] {pU : U ⟶ Spec (.of K)}
  [IsCurve pU] {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU}
  {WC : WeilGroup p} (D : BoundaryDatum j WU WC) (l : ℕ) [Fact l.Prime] {V : Type u}
  [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ι : PadicAlgCl l →+* ℂ)

end BoundaryDatum

end AlgebraicGeometry
