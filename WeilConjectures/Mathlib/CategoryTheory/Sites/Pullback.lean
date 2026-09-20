/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Exactness of the pullback of sheaves, and the pullback along a composite

Let `G : C ⥤ D` be a continuous functor between sites such that the pullback functor
`CategoryTheory.Functor.sheafPullback` exists. Being a left adjoint, it preserves finite
colimits (`CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`) and, when the
coefficient category is preadditive, it is additive
(`CategoryTheory.Functor.additive_sheafPullback`).

The pushforward of sheaves along a composite of continuous functors is the composite of the
pushforwards *on the nose* (`CategoryTheory.Functor.sheafPushforwardContinuousComp` is
`Iso.refl`), but the pullback is only defined as *a* left adjoint of the pushforward, so the
pullback along a composite is merely canonically isomorphic to the composite of the pullbacks.
That isomorphism is `CategoryTheory.Functor.sheafPullbackComp`.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackComp` — the canonical isomorphism
  `(F ⋙ G)^{-1} ≅ F^{-1} ⋙ G^{-1}` of pullback functors on sheaves.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

section Exactness

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

end Exactness

section Comp

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  (F : C ⥤ D) (G : D ⥤ E) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous A K L).IsRightAdjoint]
  [((F ⋙ G).sheafPushforwardContinuous A J L).IsRightAdjoint]

/-- **The pullback of sheaves along a composite of continuous functors**: the canonical
isomorphism `(F ⋙ G)^{-1} ≅ F^{-1} ⋙ G^{-1}`, obtained from the uniqueness of left adjoints,
the pushforward along a composite being the composite of the pushforwards.

```
                     sheafPullbackComp
Sheaf J A ---------------------------------------> Sheaf L A
     |            (F ⋙ G)^{-1}                        ^
     |                                                |
     |  F^{-1}                              G^{-1}    |
     +-------------> Sheaf K A ------------------------+
```
-/
noncomputable def sheafPullbackComp :
    (F ⋙ G).sheafPullback A J L ≅ F.sheafPullback A J K ⋙ G.sheafPullback A K L :=
  Adjunction.leftAdjointUniq ((F ⋙ G).sheafAdjunctionContinuous A J L)
    ((F.sheafAdjunctionContinuous A J K).comp (G.sheafAdjunctionContinuous A K L))

/-- `CategoryTheory.Functor.sheafPullbackComp` is compatible with the units of the two
adjunctions it compares:

```
                                        (F ⋙ G)_* (sheafPullbackComp).hom
ℱ --unit--> (F ⋙ G)_* (F ⋙ G)^{-1} ℱ -----------------------------------> (F ⋙ G)_* G^{-1} F^{-1} ℱ
 |                                                                                    ^
 +-------unit-------> F_* F^{-1} ℱ ------------F_* unit--------------------> F_* G_* G^{-1} F^{-1} ℱ
```

the two rows being equal because `(F ⋙ G)_*` and `F_* ∘ G_*` are the same functor. -/
lemma unit_sheafPullbackComp_hom_app (ℱ : Sheaf J A) :
    ((F ⋙ G).sheafAdjunctionContinuous A J L).unit.app ℱ ≫
        ((F ⋙ G).sheafPushforwardContinuous A J L).map
          ((F.sheafPullbackComp G A J K L).hom.app ℱ) =
      (F.sheafAdjunctionContinuous A J K).unit.app ℱ ≫
        (F.sheafPushforwardContinuous A J K).map
          ((G.sheafAdjunctionContinuous A K L).unit.app ((F.sheafPullback A J K).obj ℱ)) :=
  NatTrans.congr_app
    (((F ⋙ G).sheafAdjunctionContinuous A J L).unit_leftAdjointUniq_hom
      ((F.sheafAdjunctionContinuous A J K).comp (G.sheafAdjunctionContinuous A K L))) ℱ

end Comp

end CategoryTheory.Functor
