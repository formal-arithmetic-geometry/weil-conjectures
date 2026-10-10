/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Postcomposition with an adjunction on sheaves

An adjunction `F ⊣ G` between coefficient categories induces, objectwise, an adjunction
`sheafCompose J F ⊣ sheafCompose J G` between the categories of sheaves on a site, whenever
both postcompositions preserve sheaves.

## Main definitions

- `CategoryTheory.Sheaf.sheafComposeAdjunction`: the adjunction.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A : Type u₂} [Category.{v₂} A] {B : Type u₃} [Category.{v₃} B] {F : A ⥤ B} {G : B ⥤ A}
  [J.HasSheafCompose F] [J.HasSheafCompose G]

/-- An adjunction `F ⊣ G` induces the adjunction `sheafCompose J F ⊣ sheafCompose J G`, with
unit and counit given objectwise by those of `F ⊣ G`. -/
@[simps! unit_app_hom counit_app_hom]
def sheafComposeAdjunction (adj : F ⊣ G) : sheafCompose J F ⊣ sheafCompose J G :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app P := ⟨Functor.whiskerLeft P.obj adj.unit⟩
          naturality P Q φ := by
            ext U
            exact adj.unit.naturality (φ.hom.app U) }
      counit :=
        { app P := ⟨Functor.whiskerLeft P.obj adj.counit⟩
          naturality P Q φ := by
            ext U
            exact adj.counit.naturality (φ.hom.app U) }
      left_triangle := by
        ext P U
        dsimp
        erw [Category.id_comp]
        exact adj.left_triangle_components (P.obj.obj U)
      right_triangle := by
        ext P U
        dsimp
        erw [Category.id_comp]
        exact adj.right_triangle_components (P.obj.obj U) }

end CategoryTheory.Sheaf
