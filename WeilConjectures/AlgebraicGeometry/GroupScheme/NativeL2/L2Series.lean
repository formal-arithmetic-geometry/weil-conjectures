/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# The $L^2$-series

Source: latest blueprint, `def-wf-l2-series` displayed defining formula;
unit `sk-def-wrp-l2-definition`, Complement (blueprint: def-wf-l2-series).

For a bounded constructible condensed Weil complex `K`, the coefficient of degree `n` is
its squared trace energy at level `n+1`.  The series is formed with Mathlib's
`PowerSeries.mk`, whose coefficients are indexed by `ℕ`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale Filter
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

/-- The real formal power series of squared Frobenius trace energies:
`φ_K(t) = ∑_{m ≥ 1} ‖f_K‖²_m t^(m-1)`, so its degree-`n` coefficient is
`complexTraceEnergy ... (n+1)`.

Source: latest blueprint, `def-wf-l2-series`, displayed defining formula and coefficient clause
(unit `sk-def-wrp-l2-definition`, Complement) (blueprint: def-wf-l2-series). -/
noncomputable def l2Series
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) : PowerSeries ℝ :=
  PowerSeries.mk (fun n ↦ complexTraceEnergy D l X₀ ι K (n + 1))

end WeilConjectures.NativeL2
