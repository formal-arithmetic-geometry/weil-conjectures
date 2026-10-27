/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Finite.Defs

/-!
# Finite signed elimination forms and their necessary inequalities

Source: the agent-written auxiliary assertion extracted from
`lem-trf-rational-cone-dual-finite`, old proof steps 3--4. ILO, Travaux de Gabber,
Exposé VIII, Remark 3.1.29, printed p. 103, provides toric context only.
(blueprint: lem-trf-rational-ray-elimination-forward)

The disjoint-union index retains repeated forms and allows each sign block to be empty.
-/

@[expose] public section

set_option autoImplicit false

universe u w

namespace Weil

/-- The index `I₀ ⊔ (I₊ ⊔ (I₊ × I₋))` of the signed elimination family, with `aᵢ = fᵢ(v)`.
Source: the agent-written auxiliary assertion from `lem-trf-rational-cone-dual-finite`,
old proof steps 3--4; ILO VIII Remark 3.1.29, p. 103, is contextual only.
(blueprint: lem-trf-rational-ray-elimination-forward) -/
def rationalRayEliminationIndex {V : Type u} [AddCommGroup V] [Module ℚ V]
    {I : Type w} (f : I → V →ₗ[ℚ] ℚ) (v : V) : Type w :=
  {i : I // f i v = 0} ⊕
    ({i : I // 0 < f i v} ⊕ ({i : I // 0 < f i v} × {j : I // f j v < 0}))

/-- The family consisting of `fₕ` for zero coefficients, `fᵢ` for positive coefficients,
and `aᵢ • fⱼ - aⱼ • fᵢ` for positive/negative pairs. Each value is a rational linear map.
Source: the agent-written auxiliary assertion from `lem-trf-rational-cone-dual-finite`,
old proof steps 3--4; ILO VIII Remark 3.1.29, p. 103, is contextual only.
(blueprint: lem-trf-rational-ray-elimination-forward) -/
def rationalRayEliminationFamily {V : Type u} [AddCommGroup V] [Module ℚ V]
    {I : Type w} (f : I → V →ₗ[ℚ] ℚ) (v : V) :
    rationalRayEliminationIndex f v → V →ₗ[ℚ] ℚ
  | Sum.inl h => f h.val
  | Sum.inr (Sum.inl i) => f i.val
  | Sum.inr (Sum.inr (i, j)) => (f i.val v) • f j.val - (f j.val v) • f i.val

/-- The signed elimination family is finite, and every nonnegative residual witness
satisfies all its inequalities.
Source: the agent-written auxiliary assertion from `lem-trf-rational-cone-dual-finite`,
old proof steps 3--4; ILO VIII Remark 3.1.29, p. 103, is contextual only.
(blueprint: lem-trf-rational-ray-elimination-forward)

1. The zero, positive and negative sign classes are subtypes of finite `I`. Their finite
   products and disjoint unions give a finite index. The first two blocks are given linear
   maps, and the third consists of scalar multiples and differences of linear maps.
2. Fix `x` and `t ≥ 0` with every residual `fᵢ(x) - t aᵢ ≥ 0`. For a zero coefficient,
   `fₕ(x)` equals its residual. For a positive coefficient, `t aᵢ ≥ 0`, so
   `fᵢ(x) = (fᵢ(x) - t aᵢ) + t aᵢ ≥ 0`.
3. For a positive/negative pair, `aᵢ > 0` and `-aⱼ > 0`. The sum
   `aᵢ (fⱼ(x) - t aⱼ) + (-aⱼ) (fᵢ(x) - t aᵢ)` is nonnegative. Expansion cancels the
   parameter terms and leaves `aᵢ fⱼ(x) - aⱼ fᵢ(x)`, the third-block evaluation.
4. These cover all indices. Empty blocks impose no conditions, and repeated or zero
   forms are handled separately at every index.
-/
theorem rationalRayEliminationForward {V : Type u} [AddCommGroup V] [Module ℚ V]
    {I : Type w} [Finite I] (f : I → V →ₗ[ℚ] ℚ) (v : V) :
    Finite (rationalRayEliminationIndex f v) ∧
      ∀ (x : V) (t : ℚ), 0 ≤ t → (∀ i : I, 0 ≤ f i x - t * f i v) →
        ∀ j : rationalRayEliminationIndex f v, 0 ≤ rationalRayEliminationFamily f v j x := by
  sorry

end Weil
