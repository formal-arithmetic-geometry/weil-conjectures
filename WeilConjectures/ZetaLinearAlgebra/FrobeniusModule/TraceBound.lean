/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Topology.MetricSpace.Sequences
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Weights from bounds on traces

If the power sums `∑ zᵏ` of a finite family of complex numbers are bounded by `C · Rᵏ` for all
`k ≥ 1`, then every member of the family has absolute value at most `R`. Applied to the
eigenvalues of the Frobenius, a bound `|ι tr (Fᵏ)| ≤ C · q^{kw/2}` on the traces of the powers
of the Frobenius of a Frobenius module implies that it has weights at most `w`.

## Main results

- `Complex.norm_le_of_norm_sum_pow_le`, `Multiset.norm_le_of_norm_sum_map_pow_le`: bounds on
  power sums bound the members.
- `FrobeniusModule.hasWeightsAtMost_of_norm_map_trace_pow_le`: bounds on the traces of the
  powers of the Frobenius bound the weights.
-/

@[expose] public section

universe u v

open Filter Topology

namespace FrobeniusModule

end FrobeniusModule
