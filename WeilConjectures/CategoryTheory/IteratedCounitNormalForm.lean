/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Iterated normal form for two relative counits

Source: the agent-formulated categorical calculation supporting Bhatt–Scholze,
Corollary 5.1.6, extracted from steps 5–7 of the returned proof of
`lem-weil-boundary-comparison-composition-transport`; category, functor and natural
transformation laws are Stacks Tags 0014, 001B and 001I
(blueprint: lem-weil-boundary-iterated-counit-normal-form).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

/-- Two normalized relative counits have the stated iterated normal form.

Source: the agent-formulated calculation supporting Bhatt–Scholze, Corollary 5.1.6,
in the returned proof of `lem-weil-boundary-comparison-composition-transport`, steps 5–7;
Stacks Tags 0014, 001B and 001I
(blueprint: lem-weil-boundary-iterated-counit-normal-form).

Proof (using `def-nagata-category` throughout):
1. Expand the functor images on the left by functoriality. The equation `hm` replaces
   `Pf.map (Qf.map r) ≫ m₁` with `m₀ ≫ r`, inside `Pg`.
2. Precompose `hf` with the inverse component of `Bf` at `Rf.obj (Rg.obj H)`.
   Cancel the inverse pair to replace `Pf.map b ≫ m₀` by the inverse comparison
   component followed by `SY.map ef`, then apply `Pg`.
3. Precompose `hg` with the inverse component of `Bg` at `Rg.obj H` and cancel.
   This replaces `Pg.map r ≫ mg` by that inverse followed by `SB.map eg`.
4. Naturality of `Bg` at `ef`, composed with inverse components on both sides,
   moves `Pg.map (SY.map ef)` through the inverse comparison. Combine the two
   successive `SB` images using functoriality.
5. Naturality of `Bf` at `t`, composed with its inverse components, moves
   `Pf.map (SX.map t)` through the inverse comparison; apply `Pg` to this identity.
6. Naturality of `Bg` at `Ff.map t`, composed with its inverse components,
   moves `Pg.map (SY.map (Ff.map t))` through the inverse comparison.
   Combine the remaining `SB` images by functoriality to obtain the right side.
-/
theorem iteratedCounitNormalForm
    (CX : Type u₁) [Category.{v₁} CX]
    (CY : Type u₂) [Category.{v₂} CY]
    (CB : Type u₃) [Category.{v₃} CB]
    (DX : Type u₄) [Category.{v₄} DX]
    (DY : Type u₅) [Category.{v₅} DY]
    (DB : Type u₆) [Category.{v₆} DB]
    (Ff : CX ⥤ CY) (Rf : CY ⥤ CX) (Fg : CY ⥤ CB) (Rg : CB ⥤ CY)
    (Pf : DX ⥤ DY) (Qf : DY ⥤ DX) (Pg : DY ⥤ DB) (Qg : DB ⥤ DY)
    (SX : CX ⥤ DX) (SY : CY ⥤ DY) (SB : CB ⥤ DB)
    (Bf : Ff ⋙ SY ≅ SX ⋙ Pf) (Bg : Fg ⋙ SB ≅ SY ⋙ Pg)
    (H : CB) (K : CX) (t : K ⟶ Rf.obj (Rg.obj H))
    (ef : Ff.obj (Rf.obj (Rg.obj H)) ⟶ Rg.obj H) (eg : Fg.obj (Rg.obj H) ⟶ H)
    (r : SY.obj (Rg.obj H) ⟶ Qg.obj (SB.obj H))
    (b : SX.obj (Rf.obj (Rg.obj H)) ⟶ Qf.obj (SY.obj (Rg.obj H)))
    (mg : Pg.obj (Qg.obj (SB.obj H)) ⟶ SB.obj H)
    (m₀ : Pf.obj (Qf.obj (SY.obj (Rg.obj H))) ⟶ SY.obj (Rg.obj H))
    (m₁ : Pf.obj (Qf.obj (Qg.obj (SB.obj H))) ⟶ Qg.obj (SB.obj H))
    (hg : Bg.hom.app (Rg.obj H) ≫ Pg.map r ≫ mg = SB.map eg)
    (hf : Bf.hom.app (Rf.obj (Rg.obj H)) ≫ Pf.map b ≫ m₀ = SY.map ef)
    (hm : Pf.map (Qf.map r) ≫ m₁ = m₀ ≫ r) :
    Pg.map (Pf.map (SX.map t ≫ b ≫ Qf.map r)) ≫ Pg.map m₁ ≫ mg =
      Pg.map (Bf.inv.app K) ≫ Bg.inv.app (Ff.obj K) ≫
        SB.map (Fg.map (Ff.map t) ≫ Fg.map ef ≫ eg) := by
  sorry

end CategoryTheory
