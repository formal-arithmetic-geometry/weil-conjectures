/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology

/-! # Functorial objectwise injective resolutions -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Remove the constant summand J(0), without assuming that J is additive.
attribute [local instance] normalized_preservesZero

private def quotientStep (K : C ⥤ C) (ι : 𝟭 C ⟶ K) : C ⥤ C where
  obj A := cokernel (ι.app A)
  map {A B} f := cokernel.map _ _ f (K.map f) (ι.naturality f).symm
  map_id A := by
    apply (cancel_epi (cokernel.π _)).1
    simp
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).1
    simp [K.map_comp]

attribute [local instance] quotientStep_preservesZero

-- Q₀(A) = A and Qₙ₊₁(A) = coker(Qₙ(A) → K(Qₙ(A))).
private def syzygy (K : C ⥤ C) (ι : 𝟭 C ⟶ K) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => syzygy K ι n ⋙ quotientStep K ι

-- The resolution term is K(Qₙ(A)); its differential factors through Qₙ₊₁(A).
private def degree (K : C ⥤ C) (ι : 𝟭 C ⟶ K) (n : ℕ) : C ⥤ C :=
  syzygy K ι n ⋙ K

set_option backward.isDefEq.respectTransparency false in
private def differential (K : C ⥤ C) (ι : 𝟭 C ⟶ K) (n : ℕ) :
    degree K ι n ⟶ degree K ι (n + 1) where
  app A := cokernel.π (ι.app ((syzygy K ι n).obj A)) ≫
    ι.app ((quotientStep K ι).obj ((syzygy K ι n).obj A))
  naturality {A B} f := by
    dsimp [degree, syzygy]
    simp only [Category.assoc]
    rw [← ι.naturality]
    simp [quotientStep]

set_option backward.defeqAttrib.useBackward true in
attribute [local instance] syzygy_preservesZero

attribute [local instance] degree_preservesZero

attribute [local instance] objectResolution_preservesZero

-- Postcomposing a cokernel differential with a mono preserves exactness.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
end

end CochainComplex
