/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleCofinalExtensionCore

/-! # Level normalization for the selected étale extension

Source: Zheng, Construction 4.1, printed pp. 21--23; Stacks 06YS and 06YT.
(blueprint: lem-pur-etale-cofinal-extension-level-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The derived selected extension has the normalized level comparison.
Source: Zheng, Construction 4.1, printed pp. 21--23; Stacks 06YS and 06YT
(blueprint: lem-pur-etale-cofinal-extension-level-normalization).

Proof plan: resolve on the actual ringed sequence site by the simultaneous flat-term
K-flat resolution. Evaluation preserves these representatives, and componentwise
scalar extension preserves their quasi-isomorphisms. The normalized derived-extension
construction therefore gives an isomorphism at every level. Its universal cochain
comparison is exactly `cofinalLevelNormalization`; the acyclic K-flat cone argument
extends the formula from flat-term representatives to arbitrary K-flat complexes. -/
theorem etaleCofinalExtension_level_normalization
    {W : Scheme.{u}} {l : ℕ} {B : Coefficients.{u} l} {r : ℕ ↪o ℕ}
    (core : CofinalExtensionCore W B r) :
    Nonempty { level : ∀ (m : ℕ) (eb : Evaluation W B.rings m)
      (er : Evaluation W (cofinalCoefficients B r).rings
        (SheafOfModules.systemNextSelected r m)),
      core.model.derived ⋙ eb.E ≅ er.E ⋙ scalarExtension
        (B.rings.map
          (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W //
      cofinalLevelNormalization (W := W) (B := B) (r := r)
        core.model core.ordinaryLevel level } := by sorry

end AlgebraicGeometry.Etale.SystemProjection
