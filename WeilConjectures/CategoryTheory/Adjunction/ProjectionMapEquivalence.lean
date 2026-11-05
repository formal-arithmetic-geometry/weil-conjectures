/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The projection map of an adjoint equivalence

Let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, and let `φ : F (T_D a b) ⟶ T_C (F a) (F b)`
be a natural transformation of bifunctors. If `F` is an equivalence and `φ` is an isomorphism,
the right adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))`
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) is an isomorphism
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isEquivalence`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

end CategoryTheory.Adjunction
