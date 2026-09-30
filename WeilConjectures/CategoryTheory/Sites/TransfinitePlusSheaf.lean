/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.TransfinitePlus
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus

/-!
# The transfinite plus construction is a sheaf

Let `A` be a category with a `κ`-presentable detector `G`, for a regular cardinal `κ`, and let
`J` be a Grothendieck topology on a small category `C` with fewer than `κ` arrows. We show that
the transfinite plus construction `(J.transfinitePlus A κ).obj P` is a sheaf for every presheaf
`P` (`CategoryTheory.GrothendieckTopology.isSheaf_transfinitePlus_obj`). This applies to
Grothendieck abelian categories, where any separator is a detector
(`CategoryTheory.GrothendieckTopology.isSheaf_transfinitePlus_obj_of_isSeparator`).

Write `P^{(i)}` for the stages. For a cover `S` of `X`, the sheaf condition asks that
`u : Q(X) ⟶ multiequalizer (S.index Q)` be an isomorphism, for `Q = P^{(κ)}`. Both sides are
`κ`-filtered colimits of the corresponding objects for the stages `P^{(i)}`: the target because
the multiequalizer is a `κ`-small limit, which commutes with `κ`-filtered colimits in the
presence of a `κ`-presentable detector
(`CategoryTheory.GrothendieckTopology.Cover.preservesColimitsOfShape_multiequalizerFunctor`). The
stagewise maps `u_i` are interleaved by maps
`v_i : multiequalizer (S.index P^{(i)}) ⟶ (P^{(i)})⁺(X) ≅ P^{(i+1)}(X)`
(`CategoryTheory.GrothendieckTopology.toMultiequalizer_ι_diagram` and
`CategoryTheory.GrothendieckTopology.ι_diagram_toMultiequalizer_plusObj`), so the map of
colimits is an isomorphism by `CategoryTheory.Limits.IsColimit.isIso_of_interleave`.

Since the unit `P ⟶ P^{(κ)}` is inverted by every sheaf, the transfinite plus construction is
then a left exact left adjoint to the inclusion of sheaves into presheaves
(`CategoryTheory.GrothendieckTopology.transfinitePlusAdjunction`), i.e. a sheafification functor.
-/

@[expose] public section

universe w w' u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

/-- If `C` has fewer than `κ` arrows and `D` has a `κ`-presentable detector, then the functor
`P ↦ multiequalizer (S.index P)` preserves `κ`-filtered colimits. -/
lemma Cover.preservesColimitsOfShape_multiequalizerFunctor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {D : Type w} [Category.{w'} D]
    [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
    {X : C} (S : J.Cover X) [HasLimitsOfShape (WalkingMulticospan S.shape) D]
    {G : D} (hG : IsDetector G) (κ : Cardinal.{w'}) [Fact κ.IsRegular]
    [IsCardinalPresentable G κ] (K : Type w') [SmallCategory K] [IsCardinalFiltered K κ]
    [HasColimitsOfShape K D] (hC : HasCardinalLT (CategoryTheory.Arrow C) κ) :
    PreservesColimitsOfShape K (S.multiequalizerFunctor D) := by
  have := preservesColimitsOfShape_lim_of_isDetector hG κ K
    (S.hasCardinalLT_arrow_walkingMulticospan hC)
  have : PreservesColimitsOfShape K
      ((Functor.whiskeringLeft _ _ D).obj (S.index (𝟭 Cᵒᵖ)).multicospan) :=
    preservesColimitsOfShape_of_evaluation _ _ fun j ↦
      inferInstanceAs (PreservesColimitsOfShape K ((evaluation _ D).obj _))
  exact preservesColimitsOfShape_of_natIso (S.multiequalizerFunctorIso D).symm

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
  {A : Type u} [Category.{v} A] (κ : Cardinal.{v}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- If `A` has a `κ`-presentable detector and `C` has fewer than `κ` arrows, then the
transfinite plus construction `P^{(κ)}` of any presheaf `P` is a sheaf. -/
theorem isSheaf_transfinitePlus_obj
    [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A] [HasIterationOfShape κ.ord.ToType A]
    [HasColimitsOfShape κ.ord.ToType A]
    [∀ (X : C) (S : J.Cover X), HasLimitsOfShape (WalkingMulticospan S.shape) A]
    {G : A} (hG : IsDetector G) [IsCardinalPresentable G κ] (hC : HasCardinalLT (Arrow C) κ)
    (P : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J ((J.transfinitePlus A κ).obj P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  let F := J.transfinitePlusDiagram A κ ⋙ (evaluation _ _).obj P
  have := S.preservesColimitsOfShape_multiequalizerFunctor hG κ κ.ord.ToType hC
  have hc := J.isColimitTransfinitePlusObj A κ P
  let e (i : κ.ord.ToType) := (J.transfinitePlusStageSuccIso A κ i).app P
  refine IsColimit.isIso_of_interleave (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc)
    (isColimitOfPreserves (S.multiequalizerFunctor A) hc)
    (Functor.whiskerLeft F (S.toMultiequalizerNatTrans A))
    (fun i ↦ colimit.ι (J.diagram (F.obj i) X) (op S) ≫ (e i).inv.app (op X)) (fun i ↦ ?_)
    (fun i ↦ ?_) _ (fun i ↦ ?_)
  · simp [F, e, transfinitePlusDiagram_map_succ_app, toMultiequalizer_ι_diagram_assoc]
  · rw [Functor.comp_map, Functor.comp_map, evaluation_obj_map,
      transfinitePlusDiagram_map_succ_app, Functor.map_comp,
      ← ι_diagram_toMultiequalizer_plusObj ((J.transfinitePlusStage A κ i).obj P),
      Functor.whiskerLeft_app, Cover.toMultiequalizerNatTrans_app, Category.assoc,
      Category.assoc]
    exact congrArg (_ ≫ ·) (S.toMultiequalizer_naturality (e i).inv)
  · exact (S.toMultiequalizerNatTrans A).naturality _

/-- If `A` is Grothendieck abelian with a `κ`-presentable separator and `C` has fewer than
`κ` arrows, then the transfinite plus construction `P^{(κ)}` of any presheaf `P` is a sheaf. -/
theorem isSheaf_transfinitePlus_obj_of_isSeparator [Abelian A] [IsGrothendieckAbelian.{v} A]
    {G : A} (hG : IsSeparator G) [IsCardinalPresentable G κ] (hC : HasCardinalLT (Arrow C) κ)
    (P : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J ((J.transfinitePlus A κ).obj P) :=
  J.isSheaf_transfinitePlus_obj κ hG.isDetector hC P

section Sheafification

variable (A) [Abelian A] [IsGrothendieckAbelian.{v} A] {G : A} (hG : IsSeparator G)
  [IsCardinalPresentable G κ] (hC : HasCardinalLT (Arrow C) κ)

/-- The transfinite plus construction as a functor from presheaves to sheaves, for a
Grothendieck abelian `A` with a `κ`-presentable separator and a site with fewer than `κ`
arrows. -/
noncomputable def transfinitePlusSheaf : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  ObjectProperty.lift (Presheaf.IsSheaf J (A := A)) (J.transfinitePlus A κ)
    (J.isSheaf_transfinitePlus_obj_of_isSeparator κ hG hC)

/-- The transfinite plus construction is left adjoint to the inclusion of sheaves into
presheaves: the unit `P ⟶ P^{(κ)}` is inverted by every sheaf. -/
noncomputable def transfinitePlusAdjunction :
    J.transfinitePlusSheaf A κ hG hC ⊣ sheafToPresheaf J A :=
  Adjunction.mkOfHomEquiv
    { homEquiv P F := ((fullyFaithfulSheafToPresheaf J A).homEquiv
          (X := (J.transfinitePlusSheaf A κ hG hC).obj P) (Y := F)).trans
        (((J.W_toTransfinitePlus_app A κ P).homEquiv _ F.property :
          ((J.transfinitePlus A κ).obj P ⟶ F.obj) ≃ (P ⟶ F.obj)))
      homEquiv_naturality_left_symm {P P'} F f g := by
        rw [Equiv.symm_apply_eq]
        simp only [ObjectProperty.ι_obj, transfinitePlusSheaf, ObjectProperty.lift_obj_obj,
          Functor.FullyFaithful.homEquiv, Functor.id_obj, ObjectProperty.lift_map,
          Equiv.symm_trans, Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
          ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          ObjectProperty.isLocal.homEquiv_apply, ← (J.toTransfinitePlus A κ).naturality_assoc,
          Functor.id_map]
        exact congrArg (f ≫ ·) (((J.W_toTransfinitePlus_app A κ P').homEquiv _
          F.property).apply_symm_apply g).symm
      homEquiv_naturality_right {P} F F' f g :=
        (Category.assoc ((J.toTransfinitePlus A κ).app P) f.hom g.hom).symm }

/-- The transfinite plus construction, as a functor to sheaves, preserves finite limits: its
composite with `sheafToPresheaf J A`, which creates limits, is `J.transfinitePlus A κ`. -/
instance preservesFiniteLimits_transfinitePlusSheaf :
    PreservesFiniteLimits (J.transfinitePlusSheaf A κ hG hC) := by
  have : PreservesFiniteLimits (J.transfinitePlusSheaf A κ hG hC ⋙ sheafToPresheaf J A) :=
    inferInstanceAs (PreservesFiniteLimits (J.transfinitePlus A κ))
  exact ⟨fun K _ _ ↦ preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J A)⟩

end Sheafification

end CategoryTheory.GrothendieckTopology
