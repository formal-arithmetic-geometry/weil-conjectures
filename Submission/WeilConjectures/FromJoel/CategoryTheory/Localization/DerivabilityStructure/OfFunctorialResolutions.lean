/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Functorial left resolutions give left derivability structures

Supplement to `Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`,
migrated from the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)


variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

include hp

include hW₁ in
set_option backward.defeqAttrib.useBackward true in
lemma isLocalizedEquivalence_of_functorial_left_resolutions [Φ.IsInduced] :
    Φ.IsLocalizedEquivalence := by
  rw [← Φ.isLocalizedEquivalence_op_iff]
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  apply Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions (ρ := ρ.op)
    (NatTrans.op p) (fun _ ↦ hp _) (by simp only [hW₁]; rfl)

include hW₁ in
set_option backward.defeqAttrib.useBackward true in
lemma isLeftDerivabilityStructure_of_functorial_resolutions [W₂.IsMultiplicative]
    [Φ.IsInduced] :
    Φ.IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  exact Φ.op.isRightDerivabilityStructure_of_functorial_resolutions (ρ := ρ.op)
    (NatTrans.op p) (fun _ ↦ hp _) (by simp only [hW₁]; rfl)

end LocalizerMorphism

end CategoryTheory
