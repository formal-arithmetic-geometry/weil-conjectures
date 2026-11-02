/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2Series
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Growth of squared Frobenius traces

Source: latest blueprint, part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-and-the-growth-of-squared-traces/sk-def-wrp-l2-definition/_section.md,
both defining displays, equivalent description and Complement
(blueprint: sk-def-wrp-l2-definition).

The alternating cohomological trace and its squared energy are the existing condensed
complex constructions of `def-wf-l2-norm`. The logarithm takes values in `EReal`, with
`log 0 = -∞`. Indexing by `n + 1` expresses exactly the positive extension degrees.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale Filter
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The logarithmic growth parameter of the actual condensed Weil complex.
`ENNReal.log` sends zero energy to `-∞`; dividing by `log q` gives the base-q logarithm.
The second divisor is the positive integer `n + 1`, and the final subtraction is the
curve's dimension one. No boundedness or finiteness assumption on growth is imposed.

Source: latest blueprint, defining display for ν(K)
(blueprint: sk-def-wrp-l2-definition). -/
def growthParameter (_hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) : EReal :=
  limsup (fun n : ℕ ↦
    ENNReal.log (ENNReal.ofReal (complexTraceEnergy D l X₀ ι K (n + 1))) /
      (Real.log (D.q : ℝ) : EReal) / ((n + 1 : ℕ) : EReal)) atTop - 1

/-- The logarithmic definition is the detail node's L²-weight parameter, including
both infinite endpoints and the empty admissible parameter set.

Source: latest blueprint, equivalent description and Complement
(blueprint: sk-def-wrp-l2-definition).

Proof: use the identical finite alternating stalk traces and energies of def-wf-l2-norm.
Put b_n = log_q(S_n)/n and c = limsup b_n. If a+1 > c, choose c < u < a+1;
eventually S_n ≤ q^(nu), so the normalized energy is bounded by
(q^(u-a-1))^n and tends to zero. If a+1 < c, choose a+1 < v < c;
arbitrarily far out S_n > q^(nv), so the normalized tail suprema are infinite.
Thus all a < c-1 are admissible and no a > c-1 is admissible. Their supremum is c-1,
regardless of endpoint membership. When c = -∞ the admissible set is empty, and when
c = +∞ all real parameters are admissible. Positive reindexing does not change limsup.
This is precisely complexL2Weight's extended-real supremum. -/
theorem growthParameter_eq_complexL2Weight (hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) :
    growthParameter D l X₀ hl ι K = complexL2Weight D l X₀ ι K := by
  sorry

/-- The series in the Complement has coefficient S_(n+1) in degree n.

Source: latest blueprint, Complement, citing def-wf-l2-series
(blueprint: sk-def-wrp-l2-definition).

Proof: the existing l2Series is PowerSeries.mk of the energy sequence reindexed by n+1.
Apply PowerSeries.coeff_mk. This is exactly ∑_(m≥1) S_m t^(m-1). -/
theorem growthSeries_coeff (hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (n : ℕ) :
    PowerSeries.coeff n (l2Series D l hl X₀ ι K) =
      complexTraceEnergy D l X₀ ι K (n + 1) := by
  sorry

end WeilConjectures.NativeL2
