/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints

/-!
# Detecting a weight from the growth of the squared trace sums

For a lisse Weil sheaf `N` on a variety over `𝔽_q` the *trace energy* is the sum of the
squared complex absolute values of its trace function over the `𝔽_{qⁿ}`-points,

`S_n(X₀, N) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{N,n}(x)|²`.

Its exponential generating series is the `L`-function of `N ⊗ N^∨(w)` on a curve, hence a
ratio of two determinants, and the denominator is pure of weight `2v + 2` by the endpoint
lemma `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`. The
series has infinitely many nonzero coefficients because the summands are nonnegative and not
all zero, so at least one finite pole survives; an energy bound `S_n ≤ C q^{nB}` forces the
radius of convergence to be at least `q^{-B}`, so that pole cannot lie inside, giving
`v ≤ B - 1`. No weight estimate for `H_c^1` is used.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.traceEnergy`: the sum `S_n(X₀, N)`.
- `AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le`: the weight bound it detects.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace energy `S_n(X₀, F) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{F,n}(x)|²` of a Weil sheaf at
level `n`, the squared `L²`-norm of its trace function on the `𝔽_{qⁿ}`-points, with junk value
`0` if `X₀` has infinitely many `𝔽_{qⁿ}`-points. The intended situation is that of
`AlgebraicGeometry.Scheme.Hom.finite_fieldPoints`, where `X₀` is of finite type over the finite
field `k₀` and the index type is finite. (blueprint: `sk-l-dl-a1-energy`) -/
noncomputable def traceEnergy (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) : ℝ :=
  ∑ᶠ x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n),
    ‖ι (F.traceFunction n x)‖ ^ 2

/-- Let `N ≠ 0` be lisse on a smooth geometrically connected affine curve `V₀` of finite type
over `k₀` and punctually `ι`-pure of weight `v`. If the trace energies satisfy
`S_n(V₀, N) ≤ C q^{nB}` for every `n ≥ 1`, with `0 < C` independent of `n`, then `v ≤ B - 1`.
(blueprint: `sk-l-dl-a1-energy`) -/
theorem le_sub_one_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (N : WeilSheaf k₀ l V) (hN : ¬ Limits.IsZero N) (hlisse : N.IsLisse) {v : ℝ}
    (hpure : N.IsPunctuallyPureOfWeight ι v) {C B : ℝ} (hC : 0 < C)
    (hS : ∀ n : ℕ, 1 ≤ n → N.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B)) :
    v ≤ B - 1 := by
  sorry

end WeilSheaf

end AlgebraicGeometry
