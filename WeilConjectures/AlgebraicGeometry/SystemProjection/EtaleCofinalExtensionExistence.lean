/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleCofinalExtensionLevelNormalization

/-! # Selected extension on the actual étale sequence site

Source: Zheng, Construction 4.1; Stacks 06YS and 06YT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The local selected extension, including its ordinary unit and derived representative
normalization, exists on the actual sequence-site category.
Source: Zheng, Construction 4.1, printed p. 21; Stacks 06YS and 06YT
(blueprint: lem-pur-etale-cofinal-extension-existence).

Proof: take the transported core data and the separately constructed normalized level
comparison, then package their fields into `CofinalExtension`. -/
theorem etaleCofinalExtension_nonempty (W : Scheme.{u}) {l : ℕ}
    (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    Nonempty (CofinalExtension W B r) := by
  classical
  obtain ⟨core⟩ := etaleCofinalExtension_core_nonempty W B r
  let normalized := (etaleCofinalExtension_level_normalization core).some
  exact ⟨{ base := core.base,
            selected := core.selected,
            theory := core.theory,
            model := core.model,
            ordinary := core.ordinary,
            ordinaryLevel := core.ordinaryLevel,
            ordinaryLevel_unit := core.ordinaryLevel_unit,
            level := normalized.1,
            level_normalization := normalized.2 }⟩

end AlgebraicGeometry.Etale.SystemProjection
