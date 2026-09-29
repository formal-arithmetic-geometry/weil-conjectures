/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.Sites.TransfinitePlus
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# The transfinite plus construction is a sheaf

Let `A` be a Grothendieck abelian category with a `κ`-presentable separator `G`, for a regular
cardinal `κ`, and let `J` be a Grothendieck topology on a small category `C` with fewer than `κ`
arrows. We show that the transfinite plus construction `(J.transfinitePlus A κ).obj P` is a sheaf
for every presheaf `P` (`CategoryTheory.GrothendieckTopology.isSheaf_transfinitePlus_obj`).

Write `P^{(i)}` for the stages. For a cover `S` of `X`, the sheaf condition asks that
`u : Q(X) ⟶ multiequalizer (S.index Q)` be an isomorphism, for `Q = P^{(κ)}`. Both sides are
`κ`-filtered colimits of the corresponding objects for the stages `P^{(i)}`: the target because
the multiequalizer is a `κ`-small limit, which commutes with `κ`-filtered colimits in the
presence of a `κ`-presentable separator
(`CategoryTheory.GrothendieckTopology.Cover.preservesColimitsOfShape_multiequalizerFunctor`). The
stagewise maps `u_i` are interleaved by maps
`v_i : multiequalizer (S.index P^{(i)}) ⟶ (P^{(i)})⁺(X) ≅ P^{(i+1)}(X)`
(`CategoryTheory.GrothendieckTopology.toMultiequalizer_ι_diagram` and
`CategoryTheory.GrothendieckTopology.ι_diagram_toMultiequalizer_plusObj`), so the map of
colimits is an isomorphism by `CategoryTheory.Limits.IsColimit.isIso_of_succ`.
-/

@[expose] public section

universe w w' u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

section Plus

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type w} [Category.{w'} D]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

set_option backward.isDefEq.respectTransparency false in
/-- The map `P(X) ⟶ P⁺(X)` factors as `S.toMultiequalizer P` followed by the coprojection
of the `S`-component, for every cover `S` of `X`. -/
@[reassoc]
lemma toMultiequalizer_ι_diagram (P : Cᵒᵖ ⥤ D) {X : C} (S : J.Cover X) :
    S.toMultiequalizer P ≫ colimit.ι (J.diagram P X) (op S) = (J.toPlus P).app (op X) := by
  dsimp only [toPlus]
  rw [← colimit.w _ (homOfLE (le_top : S ≤ ⊤)).op, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ fun I ↦ ?_
  simp [Cover.Arrow.map]

set_option backward.isDefEq.respectTransparency false in
/-- The `S`-component `multiequalizer (S.index P) ⟶ P⁺(X)` of `P⁺(X)`, followed by the map
`S.toMultiequalizer P⁺`, is the map of multiequalizers induced by `J.toPlus P : P ⟶ P⁺`. -/
@[reassoc]
lemma ι_diagram_toMultiequalizer_plusObj (P : Cᵒᵖ ⥤ D) {X : C} (S : J.Cover X) :
    colimit.ι (J.diagram P X) (op S) ≫ S.toMultiequalizer (J.plusObj P) =
      (J.diagramNatTrans (J.toPlus P) X).app (op S) := by
  refine Multiequalizer.hom_ext _ _ _ fun (I : S.Arrow) ↦ ?_
  simp only [Category.assoc, Multiequalizer.lift_ι, diagramNatTrans_app]
  erw [Multiequalizer.lift_ι]
  have h : (⊤ : J.Cover I.Y) ≤ S.pullback I.f := fun _ g _ ↦ S.1.downward_closed I.hf g
  have hmap : (J.plusObj P).map I.f.op = colimMap (J.diagramPullback P I.f) ≫
      colimit.pre (J.diagram P I.Y) (J.pullback I.f).op := rfl
  rw [hmap, ι_colimMap_assoc, colimit.ι_pre]
  erw [← colimit.w (J.diagram P I.Y) (homOfLE h).op]
  dsimp only [toPlus]
  simp only [← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ fun (K : (⊤ : J.Cover I.Y).Arrow) ↦ ?_
  convert! Multiequalizer.condition (S.index P)
    { fst := ⟨K.Y, K.f ≫ I.f, S.1.downward_closed I.hf K.f⟩, snd := I, r.Z := K.Y,
      r.g₁ := 𝟙 K.Y, r.g₂ := K.f } using 1
  · simp only [Functor.comp_obj, Functor.op_obj, diagramPullback_app, homOfLE_leOfHom,
      diagram_map, Quiver.Hom.unop_op, Category.assoc, limit.lift_π, Multifork.ofι_π_app,
      Cover.index_fst, op_id]
    erw [Multiequalizer.lift_ι, P.map_id, Category.comp_id]
    rfl
  · rw [Category.assoc]
    erw [Multiequalizer.lift_ι]
    rfl

end Plus

section Multiequalizer

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type w} [Category.{w'} D]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  {X : C} (S : J.Cover X)

set_option backward.isDefEq.respectTransparency false in
variable (D) in
/-- The maps `S.toMultiequalizer P : P(X) ⟶ multiequalizer (S.index P)`, as a natural
transformation in the presheaf `P`. -/
@[simps]
noncomputable def Cover.toMultiequalizerNatTrans :
    (evaluation Cᵒᵖ D).obj (op X) ⟶ J.diagramFunctor D X ⋙ (evaluation _ D).obj (op S) where
  app P := S.toMultiequalizer P
  naturality P Q η := Multiequalizer.hom_ext _ _ _ fun I ↦ by
    simp only [Category.assoc]
    erw [Multiequalizer.lift_ι, Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc]
    exact (η.naturality I.f.op).symm

variable [HasLimitsOfShape (WalkingMulticospan S.shape) D]

set_option backward.isDefEq.respectTransparency false in
variable (D) in
/-- The functor `P ↦ multiequalizer (S.index P)` is the limit of the multicospan obtained by
precomposing `P` with the multicospan `(S.index (𝟭 Cᵒᵖ)).multicospan` in `Cᵒᵖ`. -/
noncomputable def Cover.multiequalizerFunctorIso :
    J.diagramFunctor D X ⋙ (evaluation _ D).obj (op S) ≅
      (Functor.whiskeringLeft _ _ D).obj (S.index (𝟭 Cᵒᵖ)).multicospan ⋙ lim :=
  NatIso.ofComponents (fun P ↦ HasLimit.isoOfNatIso (S.multicospanComp P (𝟭 Cᵒᵖ))) fun η ↦
    limit.hom_ext fun j ↦ by
      rcases j with I | I <;>
      simp only [Functor.comp_obj, evaluation_obj_obj, Functor.whiskeringLeft_obj_obj,
        MulticospanIndex.multicospan_obj_left, MulticospanIndex.multicospan_obj_right, lim_obj,
        Functor.comp_map, diagramFunctor_map, evaluation_obj_map, diagramNatTrans_app,
        HasLimit.lift_isoOfNatIso_hom, limit.lift_π, Cone.postcompose_obj_pt,
        Cone.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj, Multifork.ofι_π_app,
        Cover.index_fst, multicospanComp_hom_app, Functor.id_obj, Iso.refl_hom, Category.assoc,
        Functor.whiskeringLeft_obj_map, lim_map, limMap_π, Functor.whiskerLeft_app,
        HasLimit.isoOfNatIso_hom_π_assoc]
      · erw [Category.comp_id, Category.id_comp]
        rfl
      · rw [← limit.w _ (WalkingMulticospan.Hom.fst I), Category.assoc]
        erw [Category.comp_id, Category.id_comp]
        exact congrArg (Multiequalizer.ι (S.index _) _ ≫ ·) (η.naturality I.r.g₁.op).symm

variable [Balanced D] {G : D} (hG : IsSeparator G) (κ : Cardinal.{w'}) [Fact κ.IsRegular]
  [IsCardinalPresentable G κ] (K : Type w') [SmallCategory K] [IsCardinalFiltered K κ]
  [HasColimitsOfShape K D]

include hG in
/-- If `C` has fewer than `κ` arrows and `D` is balanced with a `κ`-presentable separator,
then the functor `P ↦ multiequalizer (S.index P)` preserves `κ`-filtered colimits. -/
lemma Cover.preservesColimitsOfShape_multiequalizerFunctor
    (hC : HasCardinalLT (CategoryTheory.Arrow C) κ) :
    PreservesColimitsOfShape K (J.diagramFunctor D X ⋙ (evaluation _ D).obj (op S)) := by
  have := preservesColimitsOfShape_lim_of_isSeparator hG κ K
    (S.hasCardinalLT_arrow_walkingMulticospan hC)
  have : PreservesColimitsOfShape K
      ((Functor.whiskeringLeft _ _ D).obj (S.index (𝟭 Cᵒᵖ)).multicospan) :=
    preservesColimitsOfShape_of_evaluation _ _ fun j ↦
      inferInstanceAs (PreservesColimitsOfShape K ((evaluation _ D).obj _))
  exact preservesColimitsOfShape_of_natIso (S.multiequalizerFunctorIso D).symm

end Multiequalizer

section Sheaf

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
  {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  (κ : Cardinal.{v}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

set_option backward.isDefEq.respectTransparency false in
/-- If `A` is Grothendieck abelian with a `κ`-presentable separator and `C` has fewer than
`κ` arrows, then the transfinite plus construction `P^{(κ)}` of any presheaf `P` is a sheaf. -/
theorem isSheaf_transfinitePlus_obj {G : A} (hG : IsSeparator G)
    [IsCardinalPresentable G κ] (hC : HasCardinalLT (Arrow C) κ) (P : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J ((J.transfinitePlus A κ).obj P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  let D := J.transfinitePlusDiagram A κ ⋙ (evaluation _ _).obj P
  let M := J.diagramFunctor A X ⋙ (evaluation _ A).obj (op S)
  have := S.preservesColimitsOfShape_multiequalizerFunctor hG κ κ.ord.ToType hC
  have hc := J.isColimitTransfinitePlusObj A κ P
  let e (i : κ.ord.ToType) := (J.transfinitePlusStageSuccIso A κ i).app P
  have hD (i : κ.ord.ToType) :
      D.map (homOfLE (Order.le_succ i)) = J.toPlus (D.obj i) ≫ (e i).inv :=
    NatTrans.congr_app (J.transfinitePlusDiagram_map_succ A κ i) P
  refine IsColimit.isIso_of_succ (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc)
    (isColimitOfPreserves M hc) (Functor.whiskerLeft D (S.toMultiequalizerNatTrans A))
    (fun i ↦ colimit.ι (J.diagram (D.obj i) X) (op S) ≫ (e i).inv.app (op X)) (fun i ↦ ?_)
    (fun i ↦ ?_) _ (fun i ↦ ?_)
  · change S.toMultiequalizer (D.obj i) ≫ _ ≫ _ =
      (D.map (homOfLE (Order.le_succ i))).app (op X)
    rw [hD, toMultiequalizer_ι_diagram_assoc]
    rfl
  · change _ = M.map (D.map _)
    rw [hD, M.map_comp, Category.assoc]
    erw [(S.toMultiequalizerNatTrans A).naturality (e i).inv]
    exact ι_diagram_toMultiequalizer_plusObj_assoc (D.obj i) S _
  · exact (S.toMultiequalizerNatTrans A).naturality _

end Sheaf

end CategoryTheory.GrothendieckTopology

/--
info: 'CategoryTheory.GrothendieckTopology.isSheaf_transfinitePlus_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.isSheaf_transfinitePlus_obj
