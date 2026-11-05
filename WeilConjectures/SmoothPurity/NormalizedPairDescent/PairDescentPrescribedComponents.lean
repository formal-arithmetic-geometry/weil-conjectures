/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent

/-! # Specified components of the normalized coefficient-pair functor

Source: the existing pairDescent_with_components proof in DerivedPullbackTensorHom.
(blueprint: lem-weil-pair-descent-prescribed-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory

namespace WeilConjectures.NormalizedPairDescent
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category* (C i)]
  {D : I → Type*} [∀ i, Category* (D i)]
  (S : StageSystem C) (T : StageSystem D) (φ : ∀ i, C i ⥤ D i)

end WeilConjectures.NormalizedPairDescent
