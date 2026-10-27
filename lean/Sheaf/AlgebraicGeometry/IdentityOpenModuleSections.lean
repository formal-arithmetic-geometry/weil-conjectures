/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q92 and V9
-/
module

public import Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Module sections over a common identity open

Source: Stacks Project, sites-modules.tex, Tags 04IX and 04J0; sites-cohomology.tex,
Tag 0D6G, underived open restriction; blueprint det-sf-comp-coherence-cocycle,
Refinement isomorphisms and Independence (blueprint: lem-sfb-identity-open-module-sections).

The predicates below spell out the geometric inverse, the specified section coordinates,
and the uniqueness and coherence of the module comparisons. All functors, coefficient
maps, and section coprojections are the existing ones. No derived construction is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IdentityOpenModuleSections

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The projection isomorphisms have inverse `(1_V,j'v)`, naturally in the site object.
The two inverse projections specify that pair by the pullback universal property.
Source: Stacks 01JO and 0D6G (blueprint: lem-sfb-identity-open-module-sections). -/
def ProjectionGeometry : Prop :=
  ∀ {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z),
    j' ≫ h = j → h ⁻¹' Set.range j = Set.range j' →
    ∃ e : ∀ V : U.ProEt, pullback (V.hom ≫ j) h ≅ V.left,
      (∀ V : U.ProEt, (e V).hom = pullback.fst (V.hom ≫ j) h ∧
        (e V).inv ≫ pullback.fst (V.hom ≫ j) h = 𝟙 V.left ∧
        (e V).inv ≫ pullback.snd (V.hom ≫ j) h = V.hom ≫ j') ∧
      ∀ (V W : U.ProEt) (t : V ⟶ W),
        t.left ≫ (e W).inv = (e V).inv ≫
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map
            ((Scheme.ProEtaleOpenRestriction.objectComposition j).map t)).left

/-- Families of comparisons for exactly the commuting common-open diagrams of the node.
Source: Stacks 04J0 and 0D6G (blueprint: lem-sfb-identity-open-module-sections). -/
def Comparisons :=
  ∀ {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
    (_w : j' ≫ h = j) (_hw : h ⁻¹' Set.range j = Set.range j'),
    lowerStar Λ h ⋙ upperStar Λ j ≅ upperStar Λ j'

/-- The section formula for one comparison, in the specified adjunction-unit coordinates.
The arrow inside `M.X.obj.map` is the pair `(1_V,j'v)` into the base change, as a
morphism of the pro-etale site over `Z'`. Both coprojections are those of the actual
extension-of-scalars pullback, including its coefficient action.
Source: Stacks 04IX and 04J0 (blueprint: lem-sfb-identity-open-module-sections). -/
def Normalized {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (c : lowerStar Λ h ⋙ upperStar Λ j ≅ upperStar Λ j') : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1}) (condensedRingObj Λ Z'))
    (V : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)))),
    (c.hom.app M).hom.hom.app (op V)
        (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ h).obj M) V s) =
      ModuleOpenPasting.coprojection Λ j' M V
        (M.X.obj.map (MorphismProperty.Over.homMk
          (pullback.lift (𝟙 V.left) (V.hom ≫ j')
            ((Category.id_comp _).trans
              ((Category.assoc V.hom j' h).trans
                (congrArg (fun t : U ⟶ Z ↦ V.hom ≫ t) w)).symm))
          (pullback.lift_snd _ _ _)).op s)

/-- Open pullback is sectionwise restriction, with the existing inverse-scalar action
comparison. The bijective coprojections identify its sections with the original sections;
`inverseImageActionIso` supplies the action transported through `alpha_j` inverse.
Source: Stacks 04IX and scalar transport (blueprint: lem-sfb-identity-open-module-sections). -/
def OpenRestriction : Prop :=
  ∀ {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j],
    (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (V : U.ProEt), Function.Bijective (ModuleOpenPasting.coprojection Λ j M V)) ∧
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (V : U.ProEt)
      (s : M.X.obj.obj (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V))),
      (((ModuleOpenPasting.inverseImageActionIso Λ j).hom.app M).hom.hom.app (op V))
          (ModuleOpenPasting.coprojection Λ j M V s) =
        ((ProEtale.upperStar Ab.{u + 1} j).obj M.X).obj.map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
            inferInstance trivial).unit.app V).op
          (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X).hom.app
            (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)) s)

/-- The section formula uniquely determines each module natural isomorphism.
Source: Stacks 04J0, sectionwise faithfulness
(blueprint: lem-sfb-identity-open-module-sections). -/
def UniqueNormalized (c : Comparisons Λ) : Prop :=
  ∀ {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
    (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j'),
    Normalized Λ j j' h w (c j j' h w hw) ∧
    ∀ d : lowerStar Λ h ⋙ upperStar Λ j ≅ upperStar Λ j',
      Normalized Λ j j' h w d → d = c j j' h w hw

/-- Composition uses the inverse of the specified module lower-star compositor. The
associator and the proof of the composite common-open condition are explicit.
Source: Stacks 04J0 and 0D6E, underived compositor
(blueprint: lem-sfb-identity-open-module-sections). -/
def Composition (c : Comparisons Λ) : Prop :=
  ∀ {U Z Z' Z'' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z') (j'' : U ⟶ Z'')
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (h : Z' ⟶ Z) (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j')
    (k : Z'' ⟶ Z') (w' : j'' ≫ k = j') (hw' : k ⁻¹' Set.range j' = Set.range j''),
    (c j j'' (k ≫ h)
        ((Category.assoc j'' k h).symm.trans
          ((congrArg (fun t : U ⟶ Z' ↦ t ≫ h) w').trans w))
        ((congrArg (fun S : Set Z' ↦ k ⁻¹' S) hw).trans hw')).hom =
      Functor.whiskerRight (lowerStarComp Λ k h).inv (upperStar Λ j) ≫
        (Functor.associator (lowerStar Λ k) (lowerStar Λ h) (upperStar Λ j)).hom ≫
        Functor.whiskerLeft (lowerStar Λ k) (c j j' h w hw).hom ≫
        (c j' j'' k w' hw').hom

/-- The identity comparison agrees with the canonical sectionwise identity pushforward.
Source: Stacks 03D6 and 04J0 (blueprint: lem-sfb-identity-open-module-sections). -/
def Identity (c : Comparisons Λ) : Prop :=
  ∀ {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j],
    (c j j (𝟙 Z) (Category.comp_id j) rfl).hom =
      Functor.whiskerRight (lowerStarId Λ Z).hom (upperStar Λ j) ≫
        (Functor.leftUnitor (upperStar Λ j)).hom

private theorem commonSquare {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
    (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j') :
    IsPullback j' (𝟙 U) h j := by
  apply (IsOpenImmersion.isPullback (𝟙 U) j' j h _ _).flip
  · simpa using w
  · exact TopologicalSpace.Opens.ext hw

private theorem projectionGeometry : ProjectionGeometry.{u} := by
  intro U Z Z' j j' _ _ h w hw
  let sq := commonSquare j j' h w hw
  have hs (V : U.ProEt) :
      pullback.snd (V.hom ≫ j) h = pullback.fst (V.hom ≫ j) h ≫ V.hom ≫ j' := by
    obtain ⟨a, ha, hb⟩ := sq.exists_lift (pullback.snd (V.hom ≫ j) h)
      (pullback.fst (V.hom ≫ j) h ≫ V.hom) (by
        simpa only [Category.assoc] using (pullback.condition (f := V.hom ≫ j) (g := h)).symm)
    have hb' : a = pullback.fst (V.hom ≫ j) h ≫ V.hom := by simpa using hb
    rw [← Category.assoc, ← hb', ha]
  let e (V : U.ProEt) : pullback (V.hom ≫ j) h ≅ V.left :=
    { hom := pullback.fst _ _
      inv := pullback.lift (𝟙 V.left) (V.hom ≫ j') (by simp [w])
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          exact (hs V).symm
      inv_hom_id := by simp }
  refine ⟨e, fun V ↦ ⟨rfl, by simp [e], by simp [e]⟩, ?_⟩
  intro V W t
  apply pullback.hom_ext
  · change t.left ≫ (e W).inv ≫ pullback.fst _ _ =
      (e V).inv ≫
        pullback.lift (pullback.fst _ _ ≫ t.left) (pullback.snd _ _) _ ≫
          pullback.fst _ _
    simp only [e, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.comp_id, Category.id_comp]
  · change t.left ≫ (e W).inv ≫ pullback.snd _ _ =
      (e V).inv ≫
        pullback.lift (pullback.fst _ _ ≫ t.left) (pullback.snd _ _) _ ≫
          pullback.snd _ _
    simp only [e, pullback.lift_snd]
    rw [← Category.assoc, MorphismProperty.Over.w t]

private theorem action_unit {U Z : Scheme.{u}} (j : U ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    ((upperStarLowerStarAdjunction Λ j).unit.app M).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} j).map
          (((ModuleOpenPasting.inverseImageActionIso Λ j).hom.app M).hom) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X := by
  have hh := upperStarLowerStarAdjunction_homEquiv_hom Λ j M
    (((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ Z) ⋙
      Mod.comap (inv (condensedPullbackHom Λ j))).obj M)
    ((ModuleOpenPasting.inverseImageActionIso Λ j).hom.app M)
  rw [Adjunction.homEquiv_unit] at hh
  simp only [Mod.comp_hom', lowerStar_map_hom] at hh
  erw [extendUnitHom_extendScalarsIsoComapInv_hom_app Λ j] at hh
  exact hh.trans ((congrArg
    (fun t ↦ (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X ≫ t)
    ((ProEtale.lowerStar Ab.{u + 1} j).map_id _)).trans (Category.comp_id _))

private theorem openRestriction
    (hb : ∀ {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (V : U.ProEt), Function.Bijective (ModuleOpenPasting.coprojection Λ j M V)) :
    OpenRestriction Λ := by
  intro U Z j _
  refine ⟨hb j, ?_⟩
  intro M V s
  let a := (ModuleOpenPasting.inverseImageActionIso Λ j).hom.app M
  have hn := congrArg (fun t ↦ t
    (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
      (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)) s))
    (a.hom.hom.naturality
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      inferInstance trivial).unit.app V).op)
  simp only [ConcreteCategory.comp_apply] at hn
  dsimp only [ModuleOpenPasting.coprojection]
  refine hn.trans ?_
  apply congrArg
  exact congrArg (fun t ↦ t.hom.app
    (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)) s) (action_unit Λ j M)

@[irreducible] private noncomputable def comparison (β : ModuleOpenPasting.Comparisons Λ)
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
    (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j') :
    lowerStar Λ h ⋙ upperStar Λ j ≅ upperStar Λ j' :=
  β h j (𝟙 U) j' (commonSquare j j' h w hw) ≪≫
    Functor.isoWhiskerLeft (upperStar Λ j') (lowerStarId Λ U) ≪≫
      Functor.rightUnitor (upperStar Λ j')

private theorem coprojection_naturality {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j]
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (f : M ⟶ N) (V : U.ProEt)
    (s : M.X.obj.obj (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V))) :
    (((upperStar Λ j).map f).hom.hom.app (op V))
        (ModuleOpenPasting.coprojection Λ j M V s) =
      ModuleOpenPasting.coprojection Λ j N V
        (f.hom.hom.app (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)) s) := by
  have hn := congrArg (fun t ↦ t
    (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
      (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)) s))
    (((upperStar Λ j).map f).hom.hom.naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
        inferInstance trivial).unit.app V).op)
  simp only [ConcreteCategory.comp_apply] at hn
  refine hn.trans ?_
  apply congrArg
  exact (congrArg (fun t ↦ t.hom.hom.app
    (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj V)) s)
    ((upperStarLowerStarAdjunction Λ j).unit.naturality f)).symm

private theorem coprojection_site {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    {V W : U.ProEt} (t : V ⟶ W)
    (s : M.X.obj.obj (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj W))) :
    ((upperStar Λ j).obj M).X.obj.map t.op
        (ModuleOpenPasting.coprojection Λ j M W s) =
      ModuleOpenPasting.coprojection Λ j M V
        (M.X.obj.map ((Scheme.ProEtaleOpenRestriction.objectComposition j).map t).op s) := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    inferInstance trivial
  have hn := a.unit.naturality t
  simp only [Functor.id_map] at hn
  have hm := congrArg (fun f ↦ f s)
    (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.naturality
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).map t).op)
  simp only [ConcreteCategory.comp_apply] at hm
  dsimp only [ModuleOpenPasting.coprojection]
  change (((upperStar Λ j).obj M).X.obj.map (a.unit.app W).op ≫
    ((upperStar Λ j).obj M).X.obj.map t.op) _ = _
  rw [← Functor.map_comp, ← op_comp, hn, op_comp, Functor.map_comp]
  change ((upperStar Λ j).obj M).X.obj.map (a.unit.app V).op
    (((upperStar Λ j).obj M).X.obj.map
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).map
        ((Scheme.ProEtaleOpenRestriction.objectComposition j).map t)).op
      (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app _ s)) = _
  exact congrArg _ hm.symm

private theorem comparison_normalized (β : ModuleOpenPasting.Comparisons Λ)
    (hs : ModuleOpenPasting.Sectionwise Λ β)
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
    (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j') :
    Normalized Λ j j' h w (comparison Λ β j j' h w hw) := by
  intro M V s
  unfold comparison
  change (((lowerStarId Λ U).hom.app ((upperStar Λ j').obj M)).hom.hom.app (op V))
    (((β h j (𝟙 U) j' (commonSquare j j' h w hw)).hom.app M).hom.hom.app (op V)
      (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ h).obj M) V s)) = _
  rw [hs.2]
  rw [lowerStarId_hom_app_hom, ProEtale.lowerStarId_hom_app_hom_app]
  erw [coprojection_site Λ j' M
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app V)]
  change ModuleOpenPasting.coprojection Λ j' M V
    ((M.X.obj.map (ModuleOpenPasting.sectionArrow h j (𝟙 U) j'
      (commonSquare j j' h w hw) V).op ≫
      M.X.obj.map ((Scheme.ProEtaleOpenRestriction.objectComposition j').map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app V)).op) s) = _
  rw [← Functor.map_comp, ← op_comp]
  congr 3
  apply congrArg
  apply congrArg
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  all_goals
    change (pullback.lift (𝟙 V.left) V.hom _ ≫
      pullback.map V.hom (𝟙 U) (V.hom ≫ j) h (𝟙 V.left) j' j
        (by simp) (by simpa using w.symm)) ≫ _ = _
    simp

private theorem normalized_unique
    (hb : ∀ {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (V : U.ProEt), Function.Bijective (ModuleOpenPasting.coprojection Λ j M V))
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (c d : lowerStar Λ h ⋙ upperStar Λ j ≅ upperStar Λ j')
    (hc : Normalized Λ j j' h w c) (hd : Normalized Λ j j' h w d) : c = d := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨s, rfl⟩ := (hb j ((lowerStar Λ h).obj M) V.unop).2 s
  exact (hc M V.unop s).trans (hd M V.unop s).symm

private theorem comparison_identity (β : ModuleOpenPasting.Comparisons Λ)
    (hu : ModuleOpenPasting.Units Λ β) : Identity Λ (comparison Λ β) := by
  intro U Z j _
  unfold comparison
  exact hu.2.1 j (commonSquare j j (𝟙 Z) (Category.comp_id j) rfl)

private theorem comparison_composition (β : ModuleOpenPasting.Comparisons Λ)
    (hs : ModuleOpenPasting.Sectionwise Λ β) (hc : ModuleOpenPasting.Composition Λ) :
    Composition Λ (comparison Λ β) := by
  intro U Z Z' Z'' j j' j'' _ _ _ h w hw k w' hw'
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨s, rfl⟩ := (hs.1 j ((lowerStar Λ (k ≫ h)).obj M) V.unop).2 s
  change ((comparison Λ β j j'' (k ≫ h) _ _).hom.app M).hom.hom.app V
    (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ (k ≫ h)).obj M) V.unop s) =
    ((comparison Λ β j' j'' k w' hw').hom.app M).hom.hom.app V
      (((comparison Λ β j j' h w hw).hom.app ((lowerStar Λ k).obj M)).hom.hom.app V
        ((((upperStar Λ j).map ((lowerStarComp Λ k h).inv.app M)).hom.hom.app V)
          (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ (k ≫ h)).obj M) V.unop s)))
  rw [coprojection_naturality]
  erw [comparison_normalized Λ β hs j j' h w hw]
  erw [comparison_normalized Λ β hs j' j'' k w' hw']
  erw [comparison_normalized Λ β hs]
  erw [hc.1]
  change ModuleOpenPasting.coprojection Λ j'' M V.unop
    (M.X.obj.map _ s) =
    ModuleOpenPasting.coprojection Λ j'' M V.unop
      ((M.X.obj.map _ ≫ M.X.obj.map _ ≫ M.X.obj.map _) s)
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp only [Functor.op_map, ← op_comp]
  congr 3
  apply congrArg
  apply congrArg
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.pullbackComp,
      Category.assoc]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.pullbackComp,
      Category.assoc]

/-- The common-open comparisons are canonically the specified square mate followed
by the direct-image identity comparison.
Source: Stacks 0D6G and the canonical module pasting theorem
(blueprint: lem-sfb-identity-open-module-sections).

Use the canonical witnesses of module open pasting in the construction of
`identityOpenModuleSections`. The section, composition and unit calculations are
unchanged; substituting their mate equation computes the common-open comparison. -/
theorem identityOpenModuleSections_canonical :
    ProjectionGeometry.{u} ∧ OpenRestriction Λ ∧
      ∃ c : Comparisons Λ, UniqueNormalized Λ c ∧ Composition Λ c ∧ Identity Λ c ∧
        ∀ {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
          [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
          (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j'),
          (c j j' h w hw).hom =
            (mateEquiv (upperStarLowerStarAdjunction Λ h)
              (upperStarLowerStarAdjunction Λ (𝟙 U))
              (TwoSquare.mk _ _ _ _
                (((upperStarComp Λ (𝟙 U) j).symm ≪≫
                  upperStarCongr Λ (w.trans (Category.id_comp j).symm).symm ≪≫
                  upperStarComp Λ j' h).hom))).natTrans ≫
              Functor.whiskerLeft (upperStar Λ j') (lowerStarId Λ U).hom ≫
              (Functor.rightUnitor (upperStar Λ j')).hom := by
  obtain ⟨β, hs, hc, _ho, _hp, hu, _hd, hm⟩ :=
    ModuleOpenPasting.moduleDirectImageOpenPasting_canonical Λ
  refine ⟨projectionGeometry, openRestriction Λ hs.1, comparison Λ β, ?_,
    comparison_composition Λ β hs hc, comparison_identity Λ β hu, ?_⟩
  · intro U Z Z' j j' _ _ h w hw
    refine ⟨comparison_normalized Λ β hs j j' h w hw, ?_⟩
    intro d hd
    exact normalized_unique Λ hs.1 j j' h w d _ hd
      (comparison_normalized Λ β hs j j' h w hw)
  · intro U Z Z' j j' _ _ h w hw
    unfold comparison
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom]
    rw [hm h j (𝟙 U) j' (commonSquare j j' h w hw)]
    have he : (upperStarCongr Λ
        (w.trans (Category.id_comp j).symm)).inv =
        (upperStarCongr Λ (w.trans (Category.id_comp j).symm).symm).hom := by
      simp only [upperStarCongr, eqToIso.inv, eqToIso.hom]
    simp only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, he, Category.assoc]

/-- There is a unique sectionwise-normalized common-open module comparison, compatible
with composition and identity, for arbitrary commutative condensed coefficients.
Source: Stacks 01JO, 04IX, 04J0, 03D6 and 0D6G; blueprint Refinement isomorphisms
and Independence (blueprint: lem-sfb-identity-open-module-sections).

Proof:
1. Mathlib's open-immersion pullback criterion gives the cartesian representative
   `(j', 1_U, h, j)`. Its universal property proves that `(1_V,j'v)` is inverse
   to the first projection for each site object V, naturally in V.
2. The Sectionwise clause of module open pasting gives bijective coprojections.
   The scalar-extension unit followed by its comap-inverse comparison is identity;
   the lifted adjunction formula and naturality give the displayed action equation.
3. Apply open pasting directly to `(j',1_U,h,j)` and compose with lowerStarId on U.
   Its section formula and naturality along the identity-pullback inverse compute
   this comparison as restriction along `(1_V,j'v)`.
4. Surjectivity of coprojections and sectionwise extensionality prove uniqueness.
5. Compute the composite on a source coprojection. Naturality and the section formula
   for lowerStarComp inverse express it as three restrictions. Functoriality and
   equality of both pullback projections identify it with the direct comparison.
6. The identity-morphism Units clause of open pasting is exactly the identity law.
No properness, density, field, admissibility, quasi-compactness or derived hypothesis
is used. -/
theorem identityOpenModuleSections :
    ProjectionGeometry.{u} ∧ OpenRestriction Λ ∧
      ∃ c : Comparisons Λ, UniqueNormalized Λ c ∧ Composition Λ c ∧ Identity Λ c := by
  obtain ⟨hg, ho, c, hn, hc, hi, _hm⟩ := identityOpenModuleSections_canonical Λ
  exact ⟨hg, ho, c, hn, hc, hi⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IdentityOpenModuleSections
