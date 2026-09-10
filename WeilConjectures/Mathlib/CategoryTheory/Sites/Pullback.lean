/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Exactness of the pullback of sheaves along a continuous functor

Let `G : C ⥤ D` be a continuous functor between sites such that the pullback functor
`CategoryTheory.Functor.sheafPullback` exists. Being a left adjoint, it preserves finite
colimits (`CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`) and, when the
coefficient category is preadditive, it is additive
(`CategoryTheory.Functor.additive_sheafPullback`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The pullback of sheaves along a continuous functor is right exact, being a left
adjoint. -/
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (G.sheafPullback A J K) := by
  have := (G.sheafAdjunctionContinuous A J K).leftAdjoint_preservesColimits
  infer_instance

/-- The pullback of sheaves along a continuous functor is additive. -/
instance additive_sheafPullback [Preadditive A] : (G.sheafPullback A J K).Additive :=
  (G.sheafAdjunctionContinuous A J K).left_adjoint_additive

end CategoryTheory.Functor
