/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module
public import Sheaf.Paper.SemilinearSystemModels
/-! # Underlying additive sheaves of scalar restriction and evaluation -/
@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)

/-- Scalar restriction retains the underlying additive sheaf.
Source: Stacks 03CZ (blueprint: def-sfb-finite-underlying-evaluation). -/
def restrictionToSheafIso {R R' : Sheaf J CommRingCat.{r}} (φ : R ⟶ R') :
    res.{c, v, r} φ ⋙ SheafOfModules.toSheaf (ring J R) ≅
      SheafOfModules.toSheaf (ring J R') := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U ↦ Iso.refl _) ?_
    intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

/-- Module evaluation retains the additive pushforward along the vertical inclusion.
Source: Zheng 4.1 (blueprint: def-sfb-finite-underlying-evaluation). -/
def evaluationToSheafIso (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (n : ℕ) :
    evaluation.{c, v, r} J B τ n ⋙ SheafOfModules.toSheaf (ring J (B n)) ≅
      SheafOfModules.toSheaf (ring (coefficientSequenceTopology J) (systemRing J B τ)) ⋙
        (Prod.sectR n C).sheafPushforwardContinuous AddCommGrpCat.{r}
          J (coefficientSequenceTopology J) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U ↦ Iso.refl _) ?_
    intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl
end WeilConjectures.SemilinearSections
