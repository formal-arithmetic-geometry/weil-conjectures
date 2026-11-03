/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The unit consequence of a normalized counit square -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory

/-- The unit equation follows from the normalized counit square at F K.
Only the compact-support comparison at K needs to be invertible.
Source: blueprint clause (1), compatibility with units and counits
(blueprint: lem-sf-finite-exceptional-mate-unit).

Proof: apply the inverse target Hom bijection. Precompose with the invertible q at K.
Naturality of the target counit moves q to the far right; naturality of q at the
source unit moves q at G F K next to the mate. Substitute the assumed counit square.
The source triangle identity makes the composite the identity; the target triangle
identity does the same for the transpose of the desired unit. Cancel q at K.
The argument requires no global invertibility of q.
-/
theorem finiteExceptionalMateUnit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (QX : C ⥤ C') (QY : D ⥤ D')
    (q : F ⋙ QY ⟶ QX ⋙ F') (b : G ⋙ QX ⟶ QY ⋙ G')
    (K : C) [IsIso (q.app K)]
    (hc : q.app (G.obj (F.obj K)) ≫ F'.map (b.app (F.obj K)) ≫
        a'.counit.app (QY.obj (F.obj K)) = QY.map (a.counit.app (F.obj K))) :
    QX.map (a.unit.app K) ≫ b.app (F.obj K) ≫ G'.map (q.app K) =
      a'.unit.app (QX.obj K) := by
  apply (a'.homEquiv _ _).symm.injective
  change F'.map (QX.map (a.unit.app K) ≫ b.app (F.obj K) ≫ G'.map (q.app K)) ≫
      a'.counit.app (F'.obj (QX.obj K)) =
    F'.map (a'.unit.app (QX.obj K)) ≫ a'.counit.app (F'.obj (QX.obj K))
  erw [a'.left_triangle_components (QX.obj K)]
  apply (cancel_epi (q.app K)).mp
  simp only [Functor.map_comp, Category.assoc]
  erw [Category.comp_id (q.app K)]
  have hn' : F'.map (G'.map (q.app K)) ≫
      a'.counit.app (F'.obj (QX.obj K)) =
    a'.counit.app (QY.obj (F.obj K)) ≫ q.app K := a'.counit.naturality (q.app K)
  erw [hn']
  have hn := q.naturality (a.unit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn, reassoc_of% hc,
    ← QY.map_comp_assoc (F.map (a.unit.app K)) (a.counit.app (F.obj K)) (q.app K),
    a.left_triangle_components K]
  erw [QY.map_id]
  exact Category.id_comp _


end CategoryTheory
