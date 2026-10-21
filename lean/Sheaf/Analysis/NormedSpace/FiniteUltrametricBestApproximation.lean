/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Best approximation in finite-dimensional ultrametric subspaces

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent analytic auxiliary for the geometric norm projection;
an exact external reference is WANTED
(blueprint: lem-sfb-finite-ultrametric-best-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Padic

/-- A finite-dimensional subspace of an ultrametric normed space over a finite p-adic
extension contains a nearest point to every vector. The distance is positive outside
that subspace, without completeness of the ambient vector space.

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent analytic auxiliary; exact external reference WANTED
(blueprint: lem-sfb-finite-ultrametric-best-approximation).

Proof: Equip `E` with its recorded extending absolute value. By
`lem-weil-l-adic-extension-proper`, it is proper, hence locally compact; its absolute
value is nontrivial since the norm of `l` is `l` inverse, less than one. The homogeneous
norm restricted to `W` gives a normed space. Apply
`lem-sfb-finite-dimensional-normed-proper` (`FiniteDimensional.proper`) to see that
`C = {w : W | ‖w‖ ≤ ‖x‖}` is compact. It contains zero, including when `x = 0` or `W = 0`.
The function `f(w) = ‖x - w‖` is 1-Lipschitz by the ordinary triangle inequality,
so continuous. By `lem-sfb-compact-real-function-minimum`
(`IsCompact.exists_isMinOn`), it attains its minimum at some `w₀` in `C`.
Comparing with zero gives `f(w₀) ≤ ‖x‖`.

If `w` lies outside `C`, then `‖w‖ > ‖x‖`. Ultrametricity gives both
`f(w) ≤ max ‖x‖ ‖w‖ = ‖w‖` and `‖w‖ ≤ max ‖x‖ (f(w))`, by writing
`w = x - (x - w)`. Thus `f(w) = ‖w‖ > ‖x‖ ≥ f(w₀)`. Consequently `w₀` minimizes
`f` over all of `W`. Its value equals the infimum of the nonempty set of distances,
which is bounded below by zero. If `x ∉ W`, then `x - w₀ ≠ 0`, so definiteness
makes this minimum strictly positive. No completeness of `V` was used.
-/
theorem exists_finite_ultrametric_best_approximation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (V : Type v) [NormedAddCommGroup V] [Module E V]
    (h_hom : ∀ (a : E) (v : V),
      ‖a • v‖ = coefficientExtensionAbsoluteValue l E a * ‖v‖)
    (h_ultra : ∀ v w : V, ‖v + w‖ ≤ max ‖v‖ ‖w‖)
    (W : Submodule E V) [FiniteDimensional E W] (x : V) :
    (∃ w₀ : W, ‖x - (w₀ : V)‖ = ⨅ w : W, ‖x - (w : V)‖) ∧
      (x ∉ W → 0 < ⨅ w : W, ‖x - (w : V)‖) := by
  sorry

end Padic
