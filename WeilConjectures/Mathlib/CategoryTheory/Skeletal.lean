/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import Mathlib.CategoryTheory.Skeletal

/-!
# Complements on the skeleton of a category

We record how `CategoryTheory.Functor.mapSkeleton` acts on objects, and deduce that
naturally isomorphic functors induce the same map on skeletons.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

lemma mapSkeleton_obj (F : C ⥤ D) (x : Skeleton C) :
    F.mapSkeleton.obj x = toSkeleton (F.obj ((fromSkeleton C).obj x)) :=
  rfl

lemma mapSkeleton_obj_eq_of_natIso {F G : C ⥤ D} (e : F ≅ G) (x : Skeleton C) :
    F.mapSkeleton.obj x = G.mapSkeleton.obj x :=
  congr_toSkeleton_of_iso (e.app _)

end Functor

end CategoryTheory

end
