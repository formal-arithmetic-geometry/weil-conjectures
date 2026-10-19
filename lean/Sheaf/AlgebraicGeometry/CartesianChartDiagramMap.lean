/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartExchangeObjects

/-! # The map in the cartesian chart diagram

Source: Stacks Project, Tags 03CB and 03Q8.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

theorem chartDiagram_map_left
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S)
    (j : I) (l m : Over j) (a : m ⟶ l) :
    let k := pullback.snd f (D.obj j).hom
    let l' : pullback (D.map m.hom).left k ⟶ pullback (D.map l.hom).left k :=
      ((cartesianChartDiagram f D j).map a).left
    let l₀ : pullback (D.map m.hom).left k ⟶ pullback (D.map l.hom).left k :=
      pullback.lift
        (pullback.fst (D.map m.hom).left k ≫ (D.map a.left).left)
        (pullback.snd (D.map m.hom).left k)
        (by
          rw [Category.assoc, ← pullback.condition]
          congr 1
          rw [← Over.comp_left, ← D.map_comp, Over.w])
    l' = l₀ := by
  dsimp only
  constructor <;> intro hh <;> simpa using hh

end AlgebraicGeometry.Etale
