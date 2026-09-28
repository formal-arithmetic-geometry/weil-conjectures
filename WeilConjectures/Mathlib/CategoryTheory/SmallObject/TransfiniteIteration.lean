/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# An induction principle for transfinite iterations

Given a successor structure `Φ : SuccStruct C` and a property `P` of objects of `C` which is
closed under isomorphisms, holds for `Φ.X₀`, is preserved by `Φ.succ`, and is stable under
the colimits appearing at limit stages, every stage `(Φ.iterationFunctor J).obj j` of the
transfinite iteration of `Φ` satisfies `P`. If moreover `P` is stable under colimits of
shape `J`, then so does the iteration `Φ.iteration J`.

## Main results

* `CategoryTheory.SmallObject.SuccStruct.prop_iterationFunctor_obj`
* `CategoryTheory.SmallObject.SuccStruct.prop_iteration`

-/

@[expose] public section

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

/-- Induction principle for the stages of the transfinite iteration of a successor
structure: a property closed under isomorphisms which holds for `Φ.X₀`, is preserved by
`Φ.succ` and by the colimits at limit stages holds for every stage. -/
lemma prop_iterationFunctor_obj (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (h₀ : P Φ.X₀) (hsucc : ∀ X, P X → P (Φ.succ X))
    (hlim : ∀ (j : J), Order.IsSuccLimit j → ∀ (F : Set.Iio j ⥤ C) (c : Cocone F),
      IsColimit c → (∀ i, P (F.obj i)) → P c.pt)
    (j : J) : P ((Φ.iterationFunctor J).obj j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact P.prop_of_iso (Φ.iterationFunctorObjBotIso J).symm h₀
  | succ j hj ih =>
    exact P.prop_of_iso (Φ.iterationFunctorObjSuccIso j hj).symm (hsucc _ ih)
  | isSuccLimit j hj ih =>
    exact hlim j hj _ _ ((Φ.iterationFunctor J).isColimitOfIsWellOrderContinuous j hj)
      fun i => ih i.1 i.2

/-- If a property of objects satisfies the hypotheses of `prop_iterationFunctor_obj` and is
moreover stable under colimits of shape `J`, then it holds for the iteration `Φ.iteration J`. -/
lemma prop_iteration (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (h₀ : P Φ.X₀) (hsucc : ∀ X, P X → P (Φ.succ X))
    (hlim : ∀ (j : J), Order.IsSuccLimit j → ∀ (F : Set.Iio j ⥤ C) (c : Cocone F),
      IsColimit c → (∀ i, P (F.obj i)) → P c.pt)
    (hJ : ∀ (F : J ⥤ C) (c : Cocone F), IsColimit c → (∀ i, P (F.obj i)) → P c.pt) :
    P (Φ.iteration J) :=
  hJ _ _ (Φ.isColimitIterationCocone J) (Φ.prop_iterationFunctor_obj J P h₀ hsucc hlim)

end CategoryTheory.SmallObject.SuccStruct
