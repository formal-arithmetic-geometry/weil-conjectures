/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Intermediate finite-lifting statement for filtered category colimits. -/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Existence of a mediating arrow for the image of a stable stage pullback.
Source: Stacks Project, Sites, Tag 09YL, pullback paragraph and Hom calculation.
(blueprint: lem-weil-pbc-filtered-colimit-pullback-exists)

Proof: Lift the vertex and two legs using joint surjectivity of the object and
arrow set colimits. Pass to a common stage above these representatives and j.
Successive applications of eventual equality in the object colimit identify
all endpoints with the transitioned cospan objects. Eventual equality in the
arrow colimit makes the cone equation hold after a further transition.
The pullback is preserved by the composite transition from j, so its limiting
cone supplies a mediating arrow at this stage. Apply the cocone functor; its
transition equations and preservation of composition give both factorization
equations in V.pt. No uniqueness assertion is used here. -/
theorem filteredColimit_pullback_exists
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) {X Y Z : F.obj j} (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f g]
    (hpres : ∀ (k : J) (a : j ⟶ k),
      PreservesLimit (cospan f g) (F.map a).toFunctor) :
    ∀ (W : V.pt) (a : W ⟶ (V.ι.app j).toFunctor.obj Y)
      (b : W ⟶ (V.ι.app j).toFunctor.obj Z),
      a ≫ (V.ι.app j).toFunctor.map f = b ≫ (V.ι.app j).toFunctor.map g →
      ∃ l : W ⟶ (V.ι.app j).toFunctor.obj (pullback f g),
        l ≫ (V.ι.app j).toFunctor.map (pullback.fst f g) = a ∧
        l ≫ (V.ι.app j).toFunctor.map (pullback.snd f g) = b := by sorry

end CategoryTheory
