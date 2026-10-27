/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData

/-! # Invertibility of the derived open-extension unit -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

universe u

/-- The derived open-extension unit is invertible.

Source: Stacks Tags 03DI and 08BS; the slice-presentation and subterminality
argument used in `openProjectionInverse_isIso`.
(blueprint: lem-sf-ring-open-map-open-unit).

Proof: identify `openExtension` with a localized module extension on the
pro-etale slice. The localized module extension has invertible unit by
subterminality. Transport full faithfulness across the slice presentation and
apply `Adjunction.unit_isIso_of_L_fully_faithful` to the specified derived
adjunction. This applies to empty and identity open immersions as well. -/
theorem openDerivedAdjunction_unit_isIso
    (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (openDerivedAdjunction R j).unit := by
  sorry

end WeilConjectures.PurCompactSupport
