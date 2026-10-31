/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemCofinalData

/-! # Core data for the selected extension on the étale sequence site

Source: Zheng, Construction 4.1, printed p. 21; Stacks 06YS and 06YT.
(blueprint: lem-pur-etale-cofinal-extension-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The transported core data of a selected extension, before its level normalization.
Source: Zheng, Construction 4.1, printed p. 21; Stacks 06YS and 06YT
(blueprint: lem-pur-etale-cofinal-extension-core).

Proof plan: identify both actual section-site module categories with strict systems,
use the existing nonempty `SystemLevelLeftExtensionTheory`, and transport its selected
ordinary derived extension across these equivalences. The transported ordinary functor
is identified by the unique left-adjoint map whose unit is the tensor unit. The same
transport gives the displayed ordinary-level comparison and its sectionwise unit
formula. All choices are made from equivalences and adjoint uniqueness, so the data are
canonical up to the recorded equalities. -/
structure CofinalExtensionCore (W : Scheme.{u}) {l : ℕ}
    (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) where
  base : CofinalEncoding W B
  selected : CofinalEncoding W (cofinalCoefficients B r)
  theory : SheafOfModules.SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
    (J := W.smallEtaleTopology)
  model : SheafOfModules.SystemDerivedLeftExtension (cofinalRestriction W B r)
    (cofinalResolving (W := W) (cofinalCoefficients B r))
  ordinary : model.ordinary ⋙ base.equivalence.functor ≅
    selected.equivalence.functor ⋙
      (theory.selected (cofinalSheafRings W B) r).ordinary
  ordinaryLevel : ∀ m : ℕ,
    model.ordinary ⋙ level W B.rings m ≅
      level W (cofinalCoefficients B r).rings
        (SheafOfModules.systemNextSelected r m) ⋙
        ProEtale.etaleSheafExtendScalars
          (B.rings.map
            (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W
  ordinaryLevel_unit : cofinalOrdinaryLevelUnit (W := W) (B := B) (r := r)
    model ordinaryLevel

/-- Core selected-extension data exist on every small étale sequence site.
(blueprint: lem-pur-etale-cofinal-extension-core)

The construction is the strict-system transport described in `CofinalExtensionCore`;
the final level normalization is deliberately left to the separate normalization step. -/
theorem etaleCofinalExtension_core_nonempty (W : Scheme.{u}) {l : ℕ}
    (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    Nonempty (CofinalExtensionCore W B r) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
