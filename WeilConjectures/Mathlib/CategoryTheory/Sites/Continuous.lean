/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The counit of the sheaf-level adjunction induced by an adjunction of sites

If the unit of a site-level adjunction `F ⊣ G` between continuous functors is an
isomorphism, then the counit of the induced adjunction
`CategoryTheory.Adjunction.sheafPushforwardContinuous` between the pushforward functors
on sheaves is an isomorphism
(`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`).
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
