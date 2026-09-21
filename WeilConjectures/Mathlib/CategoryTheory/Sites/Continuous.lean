/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Complements on the pushforward of sheaves along a continuous functor

If the unit of a site-level adjunction `F ⊣ G` between continuous functors is an
isomorphism, then the counit of the induced adjunction
`CategoryTheory.Adjunction.sheafPushforwardContinuous` between the pushforward functors
on sheaves is an isomorphism
(`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`).

`CategoryTheory.Functor.sheafPushforwardContinuous` is additive
(`CategoryTheory.Functor.additive_sheafPushforwardContinuous`) and preserves all limits
that exist in the coefficient category
(`CategoryTheory.Functor.preservesLimitsOfShape_sheafPushforwardContinuous`): it is
precomposition with `F.op`, corestricted to the sheaf subcategories, and limits of sheaves
are created by `sheafToPresheaf` while limits of presheaves are computed pointwise. Note
that this does not go through the adjunction `F^* ⊣ F_*`, which needs extra hypotheses
(existence of the left Kan extensions and of sheafification).

Being precomposition with `F.op`, the pushforward also leaves the sections unchanged:
`CategoryTheory.Functor.sheafSections_obj_sheafPushforwardContinuous_obj` and
`CategoryTheory.Functor.sheafSections_map_sheafPushforwardContinuous_map` are the named bridges
across that definitional unfolding.
-/

@[expose] public section

universe w v' u' u

open CategoryTheory Category Opposite

namespace CategoryTheory

variable {C D : Type u} [Category.{w} C] [Category.{w} D]
  (E : Type u') [Category.{v'} E]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [G.IsContinuous K J]

/-- If the unit of a site-level adjunction `F ⊣ G` is an isomorphism, then the counit of
the induced sheaf-level adjunction between the pushforward functors is an isomorphism:
its components are given by applying the sheaves to the components of the unit. -/
lemma Adjunction.isIso_sheafPushforwardContinuous_counit [IsIso adj.unit] :
    IsIso (adj.sheafPushforwardContinuous (E := E) J K).counit := by
  suffices h : ∀ P, IsIso ((adj.sheafPushforwardContinuous (E := E) J K).counit.app P) from
    NatIso.isIso_of_isIso_app _
  intro P
  have : IsIso (((adj.sheafPushforwardContinuous (E := E) J K).counit.app P).hom) := by
    suffices h : ∀ c, IsIso
        ((((adj.sheafPushforwardContinuous (E := E) J K).counit.app P).hom).app c) from
      NatIso.isIso_of_isIso_app _
    intro c
    exact inferInstanceAs (IsIso (𝟙 _ ≫ P.obj.map ((adj.unit.app c.unop).op) ≫ 𝟙 _))
  have : IsIso ((sheafToPresheaf J E).map
      ((adj.sheafPushforwardContinuous (E := E) J K).counit.app P)) := this
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

end CategoryTheory

namespace CategoryTheory.Functor

open Limits

universe w₁ w₂ vC uC vD uD vA uA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (F : C ⥤ D)
  (A : Type uA) [Category.{vA} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]

/-- The pushforward of sheaves along a continuous functor preserves limits of any shape
that exists in the coefficient category. -/
instance preservesLimitsOfShape_sheafPushforwardContinuous (E : Type w₁) [Category.{w₂} E]
    [HasLimitsOfShape E A] :
    PreservesLimitsOfShape E (F.sheafPushforwardContinuous A J K) := by
  have : PreservesLimitsOfShape E
      (F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) :=
    preservesLimitsOfShape_of_natIso
      (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J A)

/-- The pushforward of sheaves along a continuous functor is left exact. -/
instance preservesFiniteLimits_sheafPushforwardContinuous [HasFiniteLimits A] :
    PreservesFiniteLimits (F.sheafPushforwardContinuous A J K) where
  preservesFiniteLimits _ := inferInstance

/-- The pushforward of sheaves along a continuous functor is additive: it is given by
precomposition with `F.op`, so on morphisms it does not change the components. -/
instance additive_sheafPushforwardContinuous [Preadditive A] :
    (F.sheafPushforwardContinuous A J K).Additive where
  map_add := by intros; ext; rfl

/-- The sections of the pushforward of a sheaf along a continuous functor `F` over an object
`T` are the sections of the sheaf itself over `F.obj T`. This is true by definition; the lemma
is the bridge across that definitional unfolding. -/
lemma sheafSections_obj_sheafPushforwardContinuous_obj (ℱ : Sheaf K A) (T : C) :
    ((sheafSections J A).obj (op T)).obj ((F.sheafPushforwardContinuous A J K).obj ℱ) =
      ((sheafSections K A).obj (op (F.obj T))).obj ℱ :=
  rfl

/-- On the sections over `T`, the pushforward of a morphism of sheaves along a continuous
functor `F` acts as the morphism itself on the sections over `F.obj T`. This is true by
definition; the lemma is the bridge across that definitional unfolding. -/
lemma sheafSections_map_sheafPushforwardContinuous_map {ℱ 𝒢 : Sheaf K A} (α : ℱ ⟶ 𝒢) (T : C) :
    ((sheafSections J A).obj (op T)).map ((F.sheafPushforwardContinuous A J K).map α) =
      ((sheafSections K A).obj (op (F.obj T))).map α :=
  rfl

end CategoryTheory.Functor
