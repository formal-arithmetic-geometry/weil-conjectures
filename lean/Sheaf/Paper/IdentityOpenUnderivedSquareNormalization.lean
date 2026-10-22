/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Paper.CartesianCoefficients
import Mathlib.Tactic
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Underived identity-open normalization and its pullback square

Source: Stacks Project, sites-modules.tex, Tags 04J0 and 03D8;
sites-cohomology.tex, Tag 07A7; blueprint main-20261015,
det-sf-comp-composition-base-change, proof (3)
(blueprint: lem-sfb-identity-open-underived-square-normalization).

The restriction map, section arrows, and inverse pullback compositor are the existing
canonical constructions. The predicate below packages their normalization, including
the tensor-unit section calculation. The square uses exactly the termwise images of
the same compositors, on ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The sectionwise identity, tensor-unit, unit and adjunct normalizations for the
specified module adjunction on an identity open. The coprojections use the actual
module-adjunction units, hence incorporate the restricted coefficient actions.
The tensor-unit clause sends the localized unit generator `1 ⊗ m` back to `m`.
Source: Stacks 04J0 and 03D8
(blueprint: lem-sfb-identity-open-underived-square-normalization). -/
def IdentityOpenUnderivedNormalization {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (hi : i ≫ h = j)
    [IsOpenImmersion j] [IsOpenImmersion i] : Prop :=
  IsIso (identityOpenRestriction Λ j i h hi) ∧
  (∀ V : U.ProEt, IsIso (identityOpenSectionArrow j i h hi V)) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z)) (V : U.ProEt),
    Function.Bijective (openCoherenceSectionCoprojection Λ j M V)) ∧
  (∀ (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ D)) (V : U.ProEt),
    Function.Bijective (openCoherenceSectionCoprojection Λ i N V)) ∧
  (∀ (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ D)) (V : U.ProEt)
    (s : N.X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj
      ((MorphismProperty.Over.map (f := j) ⊤
        (inferInstance : WeaklyEtale j)).obj V)))),
    ((identityOpenRestriction Λ j i h hi).app N).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ j ((lowerStar Λ h).obj N) V s) =
      openCoherenceSectionCoprojection Λ i N V
        (N.X.obj.map (identityOpenSectionArrow j i h hi V).op s)) ∧
  (∀ M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z),
    (upperStar Λ j).map ((upperStarLowerStarAdjunction Λ h).unit.app M) ≫
        (identityOpenRestriction Λ j i h hi).app ((upperStar Λ h).obj M) =
      (identityOpenPullbackComparison Λ j i h hi).inv.app M) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z))
    (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ D)) (t : (upperStar Λ h).obj M ⟶ N),
    (upperStar Λ j).map
        ((upperStarLowerStarAdjunction Λ h).unit.app M ≫ (lowerStar Λ h).map t) ≫
          (identityOpenRestriction Λ j i h hi).app N =
      (identityOpenPullbackComparison Λ j i h hi).inv.app M ≫
        (upperStar Λ i).map t) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z)) (V : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.map (f := j) ⊤
      (inferInstance : WeaklyEtale j)).obj V))),
    ((identityOpenPullbackComparison Λ j i h hi).hom.app M).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ i ((upperStar Λ h).obj M) V
          (((upperStar Λ h).obj M).X.obj.map
            (identityOpenSectionArrow j i h hi V).op
            (((upperStarLowerStarAdjunction Λ h).unit.app M).hom.hom.app
              (op ((MorphismProperty.Over.map (f := j) ⊤
                (inferInstance : WeaklyEtale j)).obj V)) s))) =
      openCoherenceSectionCoprojection Λ j M V s)

/-- The path through the primed identity-open comparison, then theta and t0.
Associators merely identify the displayed iterated pullbacks.
Source: Stacks 03D8 and 07A7
(blueprint: lem-sfb-identity-open-underived-square-normalization). -/
def identityOpenSquareLeft {D Z U D' Z' U' : Scheme.{u}}
    (h : D ⟶ Z) (i : U ⟶ D)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    (hi' : i' ≫ h' = j') (sq : CommSq w h' h v) (hw : vU ≫ i = i' ≫ w) :
    upperStar Λ v ⋙ upperStar Λ j' ≅
      upperStar Λ h ⋙ upperStar Λ i ⋙ upperStar Λ vU :=
  Functor.isoWhiskerLeft _ (identityOpenPullbackComparison Λ j' i' h' hi').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openCoherencePullbackSquare Λ sq) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openCoherencePullbackSquare Λ (CommSq.mk hw))

/-- The path through s and then the unprimed identity-open comparison.
Source: Stacks 03D8 and 07A7
(blueprint: lem-sfb-identity-open-underived-square-normalization). -/
def identityOpenSquareRight {D Z U Z' U' : Scheme.{u}}
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D) (hi : i ≫ h = j)
    (v : Z' ⟶ Z) (vU : U' ⟶ U) (j' : U' ⟶ Z') (sqU : CommSq vU j' j v) :
    upperStar Λ v ⋙ upperStar Λ j' ≅
      upperStar Λ h ⋙ upperStar Λ i ⋙ upperStar Λ vU :=
  openCoherencePullbackSquare Λ sqU ≪≫
    Functor.isoWhiskerRight (identityOpenPullbackComparison Λ j i h hi).symm _ ≪≫
    Functor.associator _ _ _

section

private lemma chosen_isPullback {W X Y Z : Scheme.{u}}
    {a : W ⟶ X} {b : W ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (s : ChosenCartesianSquare a b c d) : IsPullback a b c d :=
  IsPullback.of_iso_pullback s.toCommSq s.isoPullback s.hom_fst s.hom_snd

private lemma identityOpen_baseChange {D Z U D' Z' U' : Scheme.{u}}
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D)
    (hU : IsPullback i (𝟙 U) h j)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    (sq : ChosenCartesianSquare w h' h v)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    (hi' : i' ≫ h' = j') (sqU : ChosenCartesianSquare vU j' j v)
    (hw : vU ≫ i = i' ≫ w) : IsPullback i' (𝟙 U') h' j' := by
  let q := chosen_isPullback sq
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (hi'.trans (Category.id_comp j').symm) (fun c ↦ c.snd) ?_ ?_ ?_)
  · intro c
    apply q.hom_ext
    · have hc : (c.fst ≫ w) ≫ h = (c.snd ≫ vU) ≫ j := by
        rw [Category.assoc, sq.w, ← Category.assoc, c.condition,
          Category.assoc, ← sqU.w, ← Category.assoc]
      have he := hU.lift_fst (c.fst ≫ w) (c.snd ≫ vU) hc
      have hs := hU.lift_snd (c.fst ≫ w) (c.snd ≫ vU) hc
      simp only [Category.comp_id] at hs
      rw [hs] at he
      simpa only [Category.assoc, hw] using he
    · simpa only [Category.assoc, hi'] using c.condition.symm
  · intro c
    exact Category.comp_id _
  · intro c m _ hm
    simpa only [Category.comp_id] using hm

private lemma identityOpen_unit {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (hi : i ≫ h = j)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) :
    (upperStar Λ j).map ((upperStarLowerStarAdjunction Λ h).unit.app M) ≫
      (identityOpenRestriction Λ j i h hi).app ((upperStar Λ h).obj M) =
    (identityOpenPullbackComparison Λ j i h hi).inv.app M := by
  subst j
  let sq : CommSq i (𝟙 U) h (i ≫ h) :=
    ⟨(Category.id_comp (i ≫ h)).symm⟩
  have hm := unit_mateEquiv (upperStarLowerStarAdjunction Λ h)
    (upperStarLowerStarAdjunction Λ (𝟙 U))
    (TwoSquare.mk _ _ _ _ (openCoherencePullbackSquare Λ sq).hom) M
  change (upperStar Λ (i ≫ h)).map
      ((upperStarLowerStarAdjunction Λ h).unit.app M) ≫
      (directImageOpenRestriction Λ sq).app ((upperStar Λ h).obj M) =
    (upperStarLowerStarAdjunction Λ (𝟙 U)).unit.app
        ((upperStar Λ (i ≫ h)).obj M) ≫
      (lowerStar Λ (𝟙 U)).map ((openCoherencePullbackSquare Λ sq).hom.app M) at hm
  have hu := unit_conjugateEquiv (upperStarLowerStarAdjunction Λ (𝟙 U))
    Adjunction.id (upperStarId Λ U).inv ((upperStar Λ (i ≫ h)).obj M)
  rw [← conjugateIsoEquiv_apply_inv, conjugateIsoEquiv_upperStarId] at hu
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_map,
    Category.id_comp, Iso.symm_inv] at hu
  have hc : (identityOpenRestriction Λ (i ≫ h) i h rfl).app
      ((upperStar Λ h).obj M) =
      (directImageOpenRestriction Λ sq).app ((upperStar Λ h).obj M) ≫
        (lowerStarId Λ U).hom.app ((upperStar Λ i).obj ((upperStar Λ h).obj M)) := by
    exact congrArg (fun f ↦
      (directImageOpenRestriction Λ sq).app ((upperStar Λ h).obj M) ≫ f)
      (Category.comp_id ((lowerStarId Λ U).hom.app
        ((upperStar Λ i).obj ((upperStar Λ h).obj M))))
  rw [hc, ← Category.assoc, hm, Category.assoc]
  have hn := (lowerStarId Λ U).hom.naturality
    ((openCoherencePullbackSquare Λ sq).hom.app M)
  have hn' := congrArg (fun f ↦
    (upperStarLowerStarAdjunction Λ (𝟙 U)).unit.app
      ((upperStar Λ (i ≫ h)).obj M) ≫ f) hn
  refine hn'.trans ?_
  change (upperStarLowerStarAdjunction Λ (𝟙 U)).unit.app
      ((upperStar Λ (i ≫ h)).obj M) ≫
      (lowerStarId Λ U).hom.app
        ((upperStar Λ (𝟙 U)).obj ((upperStar Λ (i ≫ h)).obj M)) ≫
      (openCoherencePullbackSquare Λ sq).hom.app M = _
  rw [← Category.assoc, hu]
  have hs : (openCoherencePullbackSquare Λ sq).hom.app M =
      (upperStarId Λ U).hom.app ((upperStar Λ (i ≫ h)).obj M) ≫
        (upperStarComp Λ i h).hom.app M := by
    change ((upperStarComp Λ (𝟙 U) (i ≫ h)).symm ≪≫
      upperStarCongr Λ (Category.id_comp (i ≫ h)) ≪≫
        upperStarComp Λ i h).hom.app M = _
    rw [upperStarComp_id_left]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    exact congrArg (fun f ↦
      (upperStarId Λ U).hom.app ((upperStar Λ (i ≫ h)).obj M) ≫ f)
      (Category.id_comp ((upperStarComp Λ i h).hom.app M))
  rw [hs, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simp only [identityOpenPullbackComparison, Iso.trans_inv, Iso.symm_inv,
    upperStarCongr_self, Iso.refl_inv, Category.id_comp]

private lemma module_unit_hom {U Z : Scheme.{u}} (j : U ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) :
    ((upperStarLowerStarAdjunction Λ j).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X ≫
        (ProEtale.lowerStar Ab.{u + 1} j).map
          (Mod.extendUnitHom (condensedPullbackHom Λ j)
            (((ProEtale.upperStar Ab.{u + 1} j).mapMod _).obj M)) := by
  simp only [upperStarLowerStarAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Mod.comp_hom', Adjunction.mapModAdjunction_unit_app_hom]
  change _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

private lemma open_section_bijective {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) (V : U.ProEt) :
    Function.Bijective (openCoherenceSectionCoprojection Λ j M V) := by
  let e := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1}
    j (inferInstance : WeaklyEtale j)
  let φ := condensedPullbackHom Λ j
  let N := ((ProEtale.upperStar Ab.{u + 1} j).mapMod _).obj M
  let t := Mod.extendUnitHom φ N
  have : (Mod.comap φ).IsEquivalence := (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have hu : IsIso (Mod.extendUnit φ N) := by
    have he : (Mod.extendRestrictAdjunction φ).unit.app N = Mod.extendUnit φ N := by
      simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_unit_app]
      change Mod.extendUnit φ N ≫ (Mod.comap φ).map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← he]
    infer_instance
  have : IsIso t := by
    change IsIso ((Mod.forget _).map (Mod.extendUnit φ N))
    infer_instance
  have hh : (e.inv.app M.X).hom.app (op V) =
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X).hom.app
        (op ((MorphismProperty.Over.map (f := j) ⊤
          (inferInstance : WeaklyEtale j)).obj V)) ≫
        ((ProEtale.upperStar Ab.{u + 1} j).obj M.X).obj.map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
            inferInstance trivial).unit.app V).op := by
    change (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).leftAdjointUniq
      (ProEtale.localizationRestrictionLowerStarAdjunction
        Ab.{u + 1} j inferInstance)).inv.app M.X).hom.app (op V) = _
    have he := ((ProEtale.localizationRestrictionLowerStarAdjunction
      Ab.{u + 1} j inferInstance).homEquiv M.X _).eq_symm_apply.mpr
        (Adjunction.homEquiv_leftAdjointUniq_hom_app
          (ProEtale.localizationRestrictionLowerStarAdjunction
            Ab.{u + 1} j inferInstance)
          (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j) M.X)
    rw [Adjunction.leftAdjointUniq_inv_app, he, Adjunction.homEquiv_counit]
    rfl
  have heq : openCoherenceSectionCoprojection Λ j M V =
      fun s ↦ ((e.inv.app M.X ≫ t).hom.app (op V)) s := by
    funext s
    dsimp only [openCoherenceSectionCoprojection]
    rw [module_unit_hom]
    change _ = (((e.inv.app M.X).hom.app (op V) ≫ t.hom.app (op V)) s)
    rw [hh]
    have hn := t.hom.naturality ((MorphismProperty.Over.mapPullbackAdj
      @WeaklyEtale ⊤ j inferInstance trivial).unit.app V).op
    exact congrArg (fun f ↦ f s)
      (congrArg (fun f ↦ ((ProEtale.upperStarLowerStarAdjunction
        Ab.{u + 1} j).unit.app M.X).hom.app
          (op ((MorphismProperty.Over.map (f := j) ⊤
            (inferInstance : WeaklyEtale j)).obj V)) ≫ f) hn.symm)
  rw [heq]
  exact ConcreteCategory.bijective_of_isIso ((e.inv.app M.X ≫ t).hom.app (op V))

private lemma open_section_naturality {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j]
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)} (f : M ⟶ N) (V : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.map (f := j) ⊤
      (inferInstance : WeaklyEtale j)).obj V))) :
    ((upperStar Λ j).map f).hom.hom.app (op V)
      (openCoherenceSectionCoprojection Λ j M V s) =
    openCoherenceSectionCoprojection Λ j N V
      (f.hom.hom.app (op ((MorphismProperty.Over.map (f := j) ⊤
        (inferInstance : WeaklyEtale j)).obj V)) s) := by
  let W : Z.ProEt := (MorphismProperty.Over.map (f := j) ⊤
    (inferInstance : WeaklyEtale j)).obj V
  let a : op ((Scheme.proEtaleBaseChange j).obj W) ⟶ op V :=
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    inferInstance trivial).unit.app V).op
  have hu := congrArg (fun t ↦ t.hom.hom.app (op W))
    ((upperStarLowerStarAdjunction Λ j).unit.naturality f)
  have hn := ((upperStar Λ j).map f).hom.hom.naturality a
  change ((upperStar Λ j).obj M).X.obj.map a ≫
      ((upperStar Λ j).map f).hom.hom.app (op V) =
    ((upperStar Λ j).map f).hom.hom.app
      (op ((Scheme.proEtaleBaseChange j).obj W)) ≫
      ((upperStar Λ j).obj N).X.obj.map a at hn
  change f.hom.hom.app (op W) ≫
      ((upperStarLowerStarAdjunction Λ j).unit.app N).hom.hom.app (op W) =
    ((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app (op W) ≫
      ((upperStar Λ j).map f).hom.hom.app
        (op ((Scheme.proEtaleBaseChange j).obj W)) at hu
  have he : ((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app (op W) ≫
      ((upperStar Λ j).obj M).X.obj.map a ≫
      ((upperStar Λ j).map f).hom.hom.app (op V) =
    f.hom.hom.app (op W) ≫
      ((upperStarLowerStarAdjunction Λ j).unit.app N).hom.hom.app (op W) ≫
      ((upperStar Λ j).obj N).X.obj.map a := by
    rw [hn, ← Category.assoc, ← hu, Category.assoc]
  exact congrArg (fun t ↦ t s) he


private lemma adjunct_of_unit {C D E : Type*}
    [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (G : C ⥤ E) (H : D ⥤ E) (c : R ⋙ G ⟶ H) (a : L ⋙ H ≅ G)
    (hu : ∀ M, G.map (adj.unit.app M) ≫ c.app (L.obj M) = a.inv.app M)
    (M : C) (N : D) (t : L.obj M ⟶ N) :
    G.map (adj.unit.app M ≫ R.map t) ≫ c.app N = a.inv.app M ≫ H.map t := by
  have hn := c.naturality t
  simp only [CategoryTheory.Functor.comp_map] at hn
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc, hu M]

omit [IsCommMonObj Λ] in
private lemma section_composite_identity {T : Scheme.{u}}
    {M N P : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)} (f : M ⟶ N) (g : N ⟶ P) (a : P ⟶ M)
    (h : (f ≫ g) ≫ a = 𝟙 M) (V : T.ProEt) (z : M.X.obj.obj (op V)) :
    a.hom.hom.app (op V) (g.hom.hom.app (op V) (f.hom.hom.app (op V) z)) = z := by
  exact congrArg (fun t ↦ t.hom.hom.app (op V) z) h

private lemma normalize_section {A B C D E : Type*}
    (a : B → A) (u : C → D) (v : A → E) (cj : C → A)
    (ck : D → E) (ci : D → B) (c : E → B)
    (he : ∀ z, a (c (v z)) = z) (hn : ∀ x, v (cj x) = ck (u x))
    (ht : ∀ y, c (ck y) = ci y) (s : C) : a (ci (u s)) = cj s := by
  rw [← ht, ← hn, he]

private lemma tensor_section_of_composite {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (hi : i ≫ h = j)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D))
    (adj : F ⊣ lowerStar Λ h)
    (c : lowerStar Λ h ⋙ upperStar Λ j ⟶ upperStar Λ i)
    (a : F ⋙ upperStar Λ i ≅ upperStar Λ j)
    (hu : ∀ M, (upperStar Λ j).map (adj.unit.app M) ≫ c.app (F.obj M) = a.inv.app M)
    (hv : ∀ (N : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)) (V : U.ProEt)
        (t : N.X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj
          ((MorphismProperty.Over.map (f := j) ⊤
            (inferInstance : WeaklyEtale j)).obj V)))),
      (c.app N).hom.hom.app (op V)
          (openCoherenceSectionCoprojection Λ j ((lowerStar Λ h).obj N) V t) =
        openCoherenceSectionCoprojection Λ i N V
          (N.X.obj.map (identityOpenSectionArrow j i h hi V).op t))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) (V : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.map (f := j) ⊤
      (inferInstance : WeaklyEtale j)).obj V))) :
    (a.hom.app M).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ i (F.obj M) V
          ((F.obj M).X.obj.map (identityOpenSectionArrow j i h hi V).op
            ((adj.unit.app M).hom.hom.app (op ((MorphismProperty.Over.map (f := j) ⊤
              (inferInstance : WeaklyEtale j)).obj V)) s))) =
      openCoherenceSectionCoprojection Λ j M V s := by
  let η := adj.unit.app M
  have he : ((upperStar Λ j).map η ≫ c.app (F.obj M)) ≫ a.hom.app M = 𝟙 _ := by
    rw [hu, Iso.inv_hom_id_app]
    rfl
  have ha := section_composite_identity Λ ((upperStar Λ j).map η)
    (c.app (F.obj M)) (a.hom.app M) he V
  let W : Z.ProEt := (MorphismProperty.Over.map (f := j) ⊤
    (inferInstance : WeaklyEtale j)).obj V
  let u : M.X.obj.obj (op W) →
      (F.obj M).X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj W)) :=
    fun t ↦ (adj.unit.app M).hom.hom.app (op W) t
  let cj := openCoherenceSectionCoprojection Λ j M V
  let ck : (F.obj M).X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj W)) →
      ((upperStar Λ j).obj ((lowerStar Λ h).obj (F.obj M))).X.obj.obj (op V) :=
    openCoherenceSectionCoprojection Λ j ((lowerStar Λ h).obj (F.obj M)) V
  let ci := fun t : (F.obj M).X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj W)) ↦
    openCoherenceSectionCoprojection Λ i (F.obj M) V
      ((F.obj M).X.obj.map (identityOpenSectionArrow j i h hi V).op t)
  let av := (a.hom.app M).hom.hom.app (op V)
  let cv := (c.app (F.obj M)).hom.hom.app (op V)
  let f := ((upperStar Λ j).map η).hom.hom.app (op V)
  have hn := open_section_naturality Λ j η V
  exact normalize_section av u f cj ck ci cv ha hn (hv (F.obj M) V) s

-- The section calculation uses the API, with the concrete functors and maps folded.
attribute [local irreducible] upperStar identityOpenRestriction identityOpenPullbackComparison

-- Match structural proofs at their positions in the predicate. In particular, the
-- coefficient construction and the predicate can cache distinct proofs of Precoherent.
-- Explicit transports avoid unfolding the category data to compare those caches.
open Lean Meta in
private meta def replaceNormalizationPath (expr : Expr) (path : List Nat)
    (replacement : Expr) : MetaM Expr := do
  match path, expr with
  | [], _ => return replacement
  | 0 :: rest, .app f x => return .app (← replaceNormalizationPath f rest replacement) x
  | 1 :: rest, .app f x => return .app f (← replaceNormalizationPath x rest replacement)
  | 2 :: rest, .forallE n d body bi =>
    return .forallE n (← replaceNormalizationPath d rest replacement) body bi
  | 3 :: rest, .forallE n d body bi =>
    return .forallE n d (← replaceNormalizationPath body rest replacement) bi
  | 2 :: rest, .lam n d body bi =>
    return .lam n (← replaceNormalizationPath d rest replacement) body bi
  | 3 :: rest, .lam n d body bi =>
    return .lam n d (← replaceNormalizationPath body rest replacement) bi
  | 4 :: rest, .mdata data body =>
    return .mdata data (← replaceNormalizationPath body rest replacement)
  | 5 :: rest, .letE n ty value body nondep =>
    return .letE n (← replaceNormalizationPath ty rest replacement) value body nondep
  | 6 :: rest, .letE n ty value body nondep =>
    return .letE n ty (← replaceNormalizationPath value rest replacement) body nondep
  | 7 :: rest, .letE n ty value body nondep =>
    return .letE n ty value (← replaceNormalizationPath body rest replacement) nondep
  | 8 :: rest, .proj n idx body =>
    return .proj n idx (← replaceNormalizationPath body rest replacement)
  | _, _ => throwError "Invalid structural-instance path"

open Lean Meta in
private meta def transportNormalizationInstances (target proof : Expr) : MetaM Expr := do
  let sourceType ← inferType proof
  let mut pending : Array (Expr × Expr × List Nat) := #[(sourceType, target, [])]
  let mut groups : Array (Expr × Expr × Array (List Nat)) := #[]
  while !pending.isEmpty do
    let (source, destination, path) := pending.back!
    pending := pending.pop
    if source == destination then continue
    if !source.hasLooseBVars && !destination.hasLooseBVars then
      if ← isProof source then
        let ty ← inferType source
        if let .const n _ := ty.getAppFn then
          if n == ``CategoryTheory.Precoherent || n == ``CategoryTheory.EssentiallySmall ||
              n == ``CategoryTheory.MorphismProperty.IsMultiplicative ||
              n == ``AlgebraicGeometry.WeaklyEtale then
            if ← isDefEq ty (← inferType destination) then
              if let some idx := groups.findIdx? fun g ↦
                  g.1 == source && g.2.1 == destination then
                let (raw, canonical, paths) := groups[idx]!
                groups := groups.set! idx (raw, canonical, paths.push path)
              else
                groups := groups.push (source, destination, #[path])
              continue
    match source, destination with
    | .mdata _ x, _ => pending := pending.push (x, destination, path ++ [4])
    | _, .mdata _ y => pending := pending.push (source, y, path)
    | .app f x, .app g y =>
      pending := pending.push (f, g, path ++ [0]) |>.push (x, y, path ++ [1])
    | .forallE _ d x _, .forallE _ e y _
    | .lam _ d x _, .lam _ e y _ =>
      pending := pending.push (d, e, path ++ [2]) |>.push (x, y, path ++ [3])
    | .letE _ ty v x _, .letE _ ty' v' y _ =>
      pending := pending.push (ty, ty', path ++ [5]) |>.push (v, v', path ++ [6])
        |>.push (x, y, path ++ [7])
    | .proj _ _ x, .proj _ _ y => pending := pending.push (x, y, path ++ [8])
    | _, _ => pure ()
  let mut result := proof
  let mut resultType := sourceType
  for (raw, canonical, paths) in groups do
    let motive ← withLocalDeclD `structuralProof (← inferType raw) fun x => do
      let mut body := resultType
      for path in paths do
        body ← replaceNormalizationPath body path x
      mkLambdaFVars #[x] body
    let nextType := motive.beta #[canonical]
    let equality ← mkAppM ``Subsingleton.elim #[raw, canonical]
    let typeEquality := mkApp6 (mkConst ``congrArg [Level.zero, Level.one])
      (← inferType raw) (mkSort Level.zero) raw canonical motive equality
    result := mkApp4 (mkConst ``Eq.mp [Level.zero])
      resultType nextType typeEquality result
    resultType := nextType
  return result

open Lean Meta in
private meta def transportNormalizationComponents (target proof : Expr) : MetaM Expr := do
  let mut restType := target
  let mut restProof := proof
  let mut parts : Array Expr := #[]
  for idx in [:8] do
    let ty ← whnf restType
    let value ← whnf restProof
    let (partType, partProof) :=
      if idx < 7 then (ty.getAppArgs[0]!, value.getAppArgs[2]!) else (ty, value)
    let part ← transportNormalizationInstances partType partProof
    unless ← isDefEq (← inferType part) partType do
      throwError "Instance transport changed component {idx + 1}"
    parts := parts.push part
    if idx < 7 then
      restType := ty.getAppArgs[1]!
      restProof := value.getAppArgs[3]!
  let mut result := parts[7]!
  for idx in [:7] do
    result ← mkAppM ``And.intro #[parts[6 - idx]!, result]
  if result.hasSorry then
    throwError "Instance transport left an unfinished proof"
  return result

set_option linter.style.multiGoal false in
private lemma identityOpen_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U D Z : Scheme.{u}} (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (hi : i ≫ h = j) (hU : IsPullback i (𝟙 U) h j) :
    IdentityOpenUnderivedNormalization Λ j i h hi := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let h ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType)
    g.setTag h.mvarId!.name
    Lean.Elab.Tactic.replaceMainGoal [h.mvarId!, g]
  · have : QuasiCompact i := MorphismProperty.of_isPullback hU.flip inferInstance
    have hrange : h ⁻¹' Set.range j = Set.range i := by
      simpa only [Set.preimage_id] using (Scheme.range_snd_of_isPullback hU.flip).symm
    have hr := identity_open_derived_restriction Λ ℓ hΛ j i h hi hrange
    have hc := hr.2.1
    have hs := hr.2.2.1
    have hv := hr.2.2.2.1
    refine ⟨hc, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · with_reducible exact open_section_bijective Λ j
    · with_reducible exact open_section_bijective Λ i
    · with_reducible exact hv
    · with_reducible exact identityOpen_unit Λ j i h hi
    · with_reducible
        exact adjunct_of_unit (upperStarLowerStarAdjunction Λ h)
          (upperStar Λ j) (upperStar Λ i) (identityOpenRestriction Λ j i h hi)
          (identityOpenPullbackComparison Λ j i h hi)
          (identityOpen_unit Λ j i h hi)
    · with_reducible
        exact tensor_section_of_composite Λ j i h hi (upperStar Λ h)
          (upperStarLowerStarAdjunction Λ h) (identityOpenRestriction Λ j i h hi)
          (identityOpenPullbackComparison Λ j i h hi) (identityOpen_unit Λ j i h hi) hv
  · run_tac Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let h : Lean.MVarId := ⟨← g.getTag⟩
      let proof ← Lean.instantiateMVars (Lean.mkMVar h)
      if proof.hasMVar then
        throwError "The normalization proof has unresolved goals"
      let proof ← transportNormalizationComponents (← g.getType) proof
      g.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

end

section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def pullbackCompTo {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : f ≫ g = fg) :
    upperStar Λ g ⋙ upperStar Λ f ≅ upperStar Λ fg :=
  (upperStarComp Λ f g).symm ≪≫ upperStarCongr Λ w

private lemma pullbackCompTo_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (fg : X ⟶ Z) (gh : Y ⟶ T) (fgh : X ⟶ T)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (ht : fg ≫ h = fgh)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ T)) :
    (upperStar Λ f).map ((pullbackCompTo Λ g h gh hgh).hom.app M) ≫
      (pullbackCompTo Λ f gh fgh
        ((congrArg (fun t ↦ f ≫ t) hgh.symm).trans
          ((Category.assoc f g h).symm.trans
            ((congrArg (fun t ↦ t ≫ h) hfg).trans ht)))).hom.app M =
    (pullbackCompTo Λ f g fg hfg).hom.app ((upperStar Λ h).obj M) ≫
      (pullbackCompTo Λ fg h fgh ht).hom.app M := by
  subst fg gh fgh
  simp only [pullbackCompTo, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    upperStarCongr_self, Iso.refl_hom, Category.comp_id]
  apply (cancel_epi ((upperStarComp Λ (f ≫ g) h).hom.app M ≫
    (upperStarComp Λ f g).hom.app ((upperStar Λ h).obj M))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rw [reassoc_of% (upperStarComp_hom_app_comp_upperStarComp_hom_app Λ f g h M)]
  simp only [← CategoryTheory.Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc, upperStarCongr_hom_app_trans,
    upperStarCongr_self, Iso.refl_hom, NatTrans.id_app]

private lemma comparison_as_comp {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (hi : i ≫ h = j) :
    identityOpenPullbackComparison Λ j i h hi = pullbackCompTo Λ i h j hi := rfl

private lemma pullbackCongr_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (upperStarCongr Λ e).symm = upperStarCongr Λ e.symm := by
  subst e
  rfl

private lemma square_as_comp {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {j : Y' ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X}
    (sq : CommSq i f' f j) :
    openCoherencePullbackSquare Λ sq =
      pullbackCompTo Λ f' j (f' ≫ j) rfl ≪≫
        (pullbackCompTo Λ i f (f' ≫ j) sq.w).symm := by
  change (upperStarComp Λ f' j).symm ≪≫
      upperStarCongr Λ sq.w.symm ≪≫ upperStarComp Λ i f =
    ((upperStarComp Λ f' j).symm ≪≫ upperStarCongr Λ (rfl : f' ≫ j = f' ≫ j)) ≪≫
      ((upperStarComp Λ i f).symm ≪≫ upperStarCongr Λ sq.w).symm
  rw [upperStarCongr_self Λ (rfl : f' ≫ j = f' ≫ j), Iso.trans_refl,
    Iso.trans_symm, Iso.symm_symm_eq, pullbackCongr_symm]

-- Keep the concrete compositor implementations folded in the cancellation calculation.
attribute [local irreducible] upperStar upperStarComp pullbackCompTo

private lemma compositor_cube {C : Type*} [Category C] {B X H K L D F Q : C}
    (p : B ≅ X) (a : B ≅ H) (b : K ≅ H) (c : K ≅ L) (d : D ≅ L)
    (e : X ≅ Q) (f : F ≅ Q) (g : D ≅ F) (r : H ≅ Q) (s : L ≅ Q)
    (h1 : a.hom ≫ r.hom = p.hom ≫ e.hom)
    (h2 : b.hom ≫ r.hom = c.hom ≫ s.hom)
    (h3 : g.hom ≫ f.hom = d.hom ≫ s.hom) :
    p.inv ≫ a.hom ≫ b.inv ≫ c.hom ≫ d.inv = e.hom ≫ f.inv ≫ g.inv := by
  apply (cancel_epi p.hom).mp
  apply (cancel_mono (d.hom ≫ s.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← h2, ← h3]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact h1

private lemma pullbackCompTo_assoc_iso {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (fg : X ⟶ Z) (gh : Y ⟶ T) (fgh : X ⟶ T)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (ht : fg ≫ h = fgh) :
    Functor.isoWhiskerRight (pullbackCompTo Λ g h gh hgh) (upperStar Λ f) ≪≫
      pullbackCompTo Λ f gh fgh
        ((congrArg (fun t ↦ f ≫ t) hgh.symm).trans
          ((Category.assoc f g h).symm.trans
            ((congrArg (fun t ↦ t ≫ h) hfg).trans ht))) =
    Functor.associator (upperStar Λ h) (upperStar Λ g) (upperStar Λ f) ≪≫
      Functor.isoWhiskerLeft (upperStar Λ h) (pullbackCompTo Λ f g fg hfg) ≪≫
      pullbackCompTo Λ fg h fgh ht := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp] using
    pullbackCompTo_assoc Λ f g h fg gh fgh hfg hgh ht M

private lemma identityOpen_square_iso {D Z U D' Z' U' : Scheme.{u}}
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D) (hi : i ≫ h = j)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    (sq : CommSq w h' h v)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    (hi' : i' ≫ h' = j') (sqU : CommSq vU j' j v)
    (hw : vU ≫ i = i' ≫ w) :
    identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq hw =
      identityOpenSquareRight Λ h j i hi v vU j' sqU := by
  let q := j' ≫ v
  have ht : (i' ≫ w) ≫ h = q := by
    dsimp only [q]
    rw [Category.assoc, sq.w, ← Category.assoc, hi']
  have h1 := congrArg Iso.hom
    (pullbackCompTo_assoc_iso Λ i' h' v j' (h' ≫ v) q hi' rfl rfl)
  have h2 := congrArg Iso.hom
    (pullbackCompTo_assoc_iso Λ i' w h (i' ≫ w) (h' ≫ v) q rfl sq.w ht)
  have h3 := congrArg Iso.hom
    (pullbackCompTo_assoc_iso Λ vU i h (i' ≫ w) j q hw hi ht)
  have hr : i' ≫ (h' ≫ v) = q :=
    (Category.assoc i' h' v).symm.trans (congrArg (fun t ↦ t ≫ v) hi')
  have hc := compositor_cube
    (Functor.associator (upperStar Λ v) (upperStar Λ h') (upperStar Λ i') ≪≫
      Functor.isoWhiskerLeft (upperStar Λ v) (pullbackCompTo Λ i' h' j' hi'))
    (Functor.isoWhiskerRight (pullbackCompTo Λ h' v (h' ≫ v) rfl) (upperStar Λ i'))
    (Functor.isoWhiskerRight (pullbackCompTo Λ w h (h' ≫ v) sq.w) (upperStar Λ i'))
    (Functor.associator (upperStar Λ h) (upperStar Λ w) (upperStar Λ i') ≪≫
      Functor.isoWhiskerLeft (upperStar Λ h) (pullbackCompTo Λ i' w (i' ≫ w) rfl))
    (Functor.associator (upperStar Λ h) (upperStar Λ i) (upperStar Λ vU) ≪≫
      Functor.isoWhiskerLeft (upperStar Λ h) (pullbackCompTo Λ vU i (i' ≫ w) hw))
    (pullbackCompTo Λ j' v q rfl)
    (pullbackCompTo Λ vU j q sqU.w)
    (Functor.isoWhiskerRight (pullbackCompTo Λ i h j hi) (upperStar Λ vU))
    (pullbackCompTo Λ i' (h' ≫ v) q hr)
    (pullbackCompTo Λ (i' ≫ w) h q ht)
    (by simpa only [Iso.trans_hom, Category.assoc] using h1)
    (by simpa only [Iso.trans_hom, Category.assoc] using h2)
    (by simpa only [Iso.trans_hom, Category.assoc] using h3)
  have hc' := congrArg
    (fun t ↦ t ≫ (Functor.associator (upperStar Λ h) (upperStar Λ i)
      (upperStar Λ vU)).hom) hc
  apply Iso.ext
  simpa only [identityOpenSquareLeft, identityOpenSquareRight, square_as_comp,
    comparison_as_comp, Functor.isoWhiskerLeft_trans, Functor.isoWhiskerRight_trans,
    ← Functor.isoWhiskerLeft_symm, ← Functor.isoWhiskerRight_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hc'

end

/-- Underived adjunction normalization over an identity open and compatibility of the
canonical pullback square, including its termwise complex and ordinary derived images.
Source: Stacks 04J0, 03D8 and 07A7; blueprint det-sf-comp-composition-base-change (3)
(blueprint: lem-sfb-identity-open-underived-square-normalization).

Proof plan (the node's nine steps):
1. Identify both open sites with the small slice sites using
lem-weil-proetale-weakly-etale-localization. Use the sectionwise internal-module
equivalence and lem-weil-pbc-localize-ringed-site-morphism. The base-change functor
preserves finite limits; on the identity open it is the identity.
2. The canonical coefficient identifications and lem-sfb-eta-comp make its restricted
structural ring map the identity. Thus c is sectionwise identity with its module action.
3. Apply lem-pur-ringed-site-pullback-localization-universes. On the localized identity
ringed site, pullback is R tensor_R -, the unit is m ↦ 1 tensor m, and the counit is
r tensor n ↦ rn. Thus the restricted unit followed by c is an isomorphism.
4. The conjugate-iso unit equation, with the specified composite adjunction, identifies
that isomorphism with the forward upperStarComp. Its inverse a is the tensor-unit map.
5. Naturality of c, composed with this unit equation, gives the adjunct equation.
6. The two Cartesian squares identify the primed inverse image with U'. Repeat 1--5;
neither properness nor density is used.
7. Conjugate associativity of the sectionwise direct-image compositors using
lem-weil-pbc-mate-pasting and the injective conjugation bijection. Both direct-image
maps preserve all fibre-product projections and the same coefficient action.
8. Reassociate for the triples (i',h',v), (i',w,h) and (vU,i,h), then cancel the common
compositors. This gives the displayed natural square equality.
9. Exact additive pullbacks preserve quasi-isomorphisms. Apply the same comparisons
termwise to complexes and localize at quasi-isomorphisms; their equality is preserved.
No underived direct image is descended termwise here. -/
theorem identity_open_underived_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {D Z U D' Z' U' : Scheme.{u}}
    [D.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [D'.Over (Spec (.of k))] [Z'.Over (Spec (.of k))] [U'.Over (Spec (.of k))]
    [LocallyOfFiniteType (D ↘ Spec (.of k))] [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (D' ↘ Spec (.of k))] [QuasiCompact (D' ↘ Spec (.of k))]
    [IsSeparated (D' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of k))] [QuasiCompact (Z' ↘ Spec (.of k))]
    [IsSeparated (Z' ↘ Spec (.of k))]
    [LocallyOfFiniteType (U' ↘ Spec (.of k))] [QuasiCompact (U' ↘ Spec (.of k))]
    [IsSeparated (U' ↘ Spec (.of k))]
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D)
    [h.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (hi : i ≫ h = j) (hU : IsPullback i (𝟙 U) h j)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    [v.IsOver (Spec (.of k))] [h'.IsOver (Spec (.of k))] [w.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare w h' h v)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    [vU.IsOver (Spec (.of k))] [j'.IsOver (Spec (.of k))] [i'.IsOver (Spec (.of k))]
    [IsOpenImmersion j'] [IsOpenImmersion i']
    (hi' : i' ≫ h' = j') (sqU : ChosenCartesianSquare vU j' j v)
    (hw : vU ≫ i = i' ≫ w) :
    IsPullback i' (𝟙 U') h' j' ∧
    IdentityOpenUnderivedNormalization Λ j i h hi ∧
    IdentityOpenUnderivedNormalization Λ j' i' h' hi' ∧
    (∀ A : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z),
      (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw).hom.app A =
        (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq).hom.app A) ∧
    (∀ P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)) ℤ,
      (NatIso.mapHomologicalComplex
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)
            (.up ℤ)).hom.app P =
        (NatIso.mapHomologicalComplex
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq) (.up ℤ)).hom.app P) ∧
    (∀ A : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)),
      (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)).hom.app A =
        (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq)).hom.app A) := by
  have _ := hp
  have _ := hpℓ
  have hpb := identityOpen_baseChange h j i hU v h' w sq vU j' i' hi' sqU hw
  have he := identityOpen_square_iso Λ h j i hi v h' w sq.toCommSq
    vU j' i' hi' sqU.toCommSq hw
  have hsquare := fun A ↦ congrArg (fun e ↦ e.hom.app A) he
  have : QuasiCompact j' :=
    MorphismProperty.of_isPullback (chosen_isPullback sqU) inferInstance
  have hnorm := identityOpen_normalization Λ ℓ hΛ j i h hi hU
  have hnorm' := identityOpen_normalization Λ ℓ hΛ j' i' h' hi' hpb
  refine ⟨hpb, hnorm, hnorm', hsquare, ?_, ?_⟩
  · intro P
    rw [he]
  · intro A
    rw [he]

end AlgebraicGeometry.ProEtale.CondensedRing
