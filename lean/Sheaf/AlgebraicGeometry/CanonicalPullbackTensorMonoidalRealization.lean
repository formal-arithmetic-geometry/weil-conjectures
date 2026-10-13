/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel

/-! # Realizing the canonical tensor comparison by a monoidal structure

Source: Stacks Project, Cohomology, Tag 079U.
(blueprint: lem-pc-canonical-pullback-tensor-monoidal-realization).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
namespace AlgebraicGeometry
attribute [local instance] pullbackDescentModuleTensor moduleSymmetric modulePreadditive
  moduleClosed moduleGrothendieck moduleResolutions moduleDerivedMonoidal pullbackDescentQLax

/-- The canonical pullback tensor comparison is the inverse tensorator of a
monoidal structure on the recorded derived pullback functor.

Proof: take the core-monoidal model of derived pullback induced by termwise
module pullback. Identify its module functor with tensor pullback by functor
extensionality. Uniqueness of left-derived functors supplies a natural
isomorphism from its counit to the shared counit. Transport the model's
monoidal structure along this natural isomorphism, including the unit.
The inverse transported tensorator is the conjugate by that isomorphism on
the input and its tensor square on the output. The counit comparison equation
shows that this tensorator satisfies the K-flat coordinate equation in
`IsCanonicalPullbackTensorComparison`: substitute the counit identity in
both factors and in the tensor input, and use naturality. Its chain comparison
is pinned by the model's degreewise module tensor equation. Naturality in
both inputs follows from that of the transported tensorator. Uniqueness of
the canonical comparison identifies this inverse tensorator with the given
family τ on all derived objects. This includes zero objects and arbitrary
unbounded inputs, by K-flat resolutions; no flatness of the morphism is used.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and the canonical model transport argument.
(blueprint: lem-pc-canonical-pullback-tensor-monoidal-realization). -/
theorem canonicalPullbackTensor_monoidal_realization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{u}} (g : T ⟶ X)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g).obj (A ⊗ B) ⟶
        (derivedPullback g).obj A ⊗ (derivedPullback g).obj B)
    (hτ : IsCanonicalPullbackTensorComparison g τ) :
    ∃ m : (derivedPullback g).CoreMonoidal,
      ∀ A B : schemeDerivedCategory X, (m.μIso A B).inv = τ A B := by
  sorry

end AlgebraicGeometry
