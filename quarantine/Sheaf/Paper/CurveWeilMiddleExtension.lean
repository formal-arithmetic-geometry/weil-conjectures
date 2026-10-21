/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Ordinary middle extension with its Weil structure

Source: blueprint main-20261015, def-wf-middle-extension
(blueprint: def-wf-middle-extension).

The published coefficient-pair realization remains available. This interface specializes
existing ordinary Weil-sheaf direct image to curves, deriving quasi-compactness from the
finite-type and separatedness hypotheses, and retaining the canonical Weil structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

/-- Ordinary j_* on Weil sheaves on curves. Its underlying sheaf functor is lowerStar,
with Frobenius transported by the canonical geometric base-change comparison.
No derived direct image or shift occurs. Quasi-compactness of j follows from the
quasi-compact structure morphism of U and the separated structure morphism of C.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
def curveWeilMiddleExtension
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {U C : Scheme.{u}} [U.Over (Spec (.of k₀))] [C.Over (Spec (.of k₀))]
    [IsCurve (U ↘ Spec (.of k₀))] [IsCurve (C ↘ Spec (.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [j.IsOver (Spec (.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l C :=
  letI : QuasiCompact (j ≫ (C ↘ Spec (.of k₀))) :=
    (comp_over j (Spec (.of k₀))).symm ▸ inferInstance
  letI := QuasiCompact.of_comp j (C ↘ Spec (.of k₀))
  directImage j

end AlgebraicGeometry.WeilSheaf
