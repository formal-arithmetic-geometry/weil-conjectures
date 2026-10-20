/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.OrdinaryCompactCohomology
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# Ordinary and compactly supported cohomology with geometric Frobenius

Source: blueprint main-20261015, def-weil-ordinary-compact-cohomology, final Weil clause
(blueprint: def-weil-ordinary-compact-cohomology).

All four existing coefficient interfaces remain publicly available. For a Qbar-Weil sheaf,
the following pair also retains the geometric Frobenius induced on cohomology by its Weil
structure. Its components are the existing ordinary and compact-support constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

/-- H^r and H_c^r of a Qbar-Weil sheaf, with their canonical geometric Frobenius.
The first uses Ra_* and the second Ra_!, followed by the r-th cohomology sheaf
and geometric-point sections. Forgetting Frobenius gives the coefficient spaces
in the ordinary/compact cohomology definition.
Source: blueprint def-weil-ordinary-compact-cohomology, final Weil clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryCompactWeilSheafCohomology
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (.of k₀))]
    [IsSeparated (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))] [QuasiCompact (X ↘ Spec (.of k₀))]
    (F : WeilSheaf k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) × FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (F.cohomology r, F.compactlySupportedCohomology r)

end AlgebraicGeometry.WeilSheaf
