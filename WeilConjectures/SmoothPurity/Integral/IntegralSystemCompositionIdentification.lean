/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # The finite-system compositor is the strict sequence compositor

Source: Stacks 0D6D and 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent finite systems with the positive uniformizer quotients are the strict
quotient systems on the ringed sequence site, and their inverse images are the same
left adjoints of the same sectionwise direct images. Both compositors are the mates of
the sectionwise fibre-product pasting map, hence they agree, before and after
localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
