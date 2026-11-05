/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The right adjoint projection map through a second adjunction

Let `adj : F ⊣ G` with `F : D ⥤ C` and let `adj' : Q ⊣ R` with `Q : C ⥤ D` be such that the
unit of the composite adjunction `F ⋙ Q ⊣ R ⋙ G` is an isomorphism; for instance `g^* ⊣ g_*`
and `i^* ⊣ i_*` for a section `i` of `g`. Composed with `G` of the unit of `adj'`, the right
adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))` is the unit of the composite adjunction
followed by `G R Q` of its transpose. This gives a criterion for the projection map to be an
isomorphism, `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_comp`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

end CategoryTheory.Adjunction
