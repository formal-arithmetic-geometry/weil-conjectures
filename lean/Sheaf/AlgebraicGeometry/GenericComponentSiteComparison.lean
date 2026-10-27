/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProfinitePointPullback

import all Sheaf.AlgebraicGeometry.AffineComponentSiteProjection
import all Sheaf.Paper.GeometricFieldProfiniteDenseSubsite
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import all Sheaf.Paper.RelativeProfiniteTestLabels

/-! # Components and geometric generic fibres

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, diagram (4.4).
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

-- Keep the explicit ring presentations and chosen site data folded during elaboration.
attribute [local irreducible] genericComponentProjection genericComponentFunctor
attribute [local irreducible] componentProjection componentStructure componentFiberHomeo

private theorem generic_geometry (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :
    IsAffine ((genericComponentFunctor T).obj E).left ∧
    RingHom.IndEtaleAcrossUniverses ((genericComponentFunctor T).obj E).hom.appTop.hom ∧
    (∀ x, IsIso (((genericComponentFunctor T).obj E).hom.stalkMap x)) ∧
    (∃ h : ((genericComponentFunctor T).obj E).left ≃ₜ
        {p : T × E.left | ConnectedComponents.mk p.1 = E.hom p.2},
      (∀ x, (h x).val.1 = ((genericComponentFunctor T).obj E).hom x) ∧
      (∀ x, (h x).val.2 = genericComponentCoordinates T E x)) := by
  have h := (affine_component_site_projection T).choose_spec.choose_spec.1 E
  unfold genericComponentFunctor genericComponentCoordinates
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private theorem genericLift_exists (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :
    ∃ g : ((genericComponentFunctor T).obj E).left ⟶ componentScheme T E,
      g ≫ componentStructure T E = ((genericComponentFunctor T).obj E).hom ∧
      ∀ x, componentProjection T E (g x) = genericComponentCoordinates T E x := by
  obtain ⟨h, hfst, hsnd⟩ := (generic_geometry T E).2.2.2
  exact component_scheme_lift (T := T)
    ((genericComponentFunctor T).obj E).hom E (genericComponentCoordinates T E) (by
      intro x
      have hx := (h x).property
      change ConnectedComponents.mk (h x).val.1 = E.hom (h x).val.2 at hx
      rwa [hfst, hsnd] at hx)

private noncomputable def genericToExplicit (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :
    (genericComponentFunctor T).obj E ⟶ (componentFunctor T).obj E :=
  MorphismProperty.Over.homMk (genericLift_exists T E).choose
    (genericLift_exists T E).choose_spec.1

private theorem genericToExplicit_coordinates (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (x : ((genericComponentFunctor T).obj E).left) :
    componentProjection T E ((genericToExplicit T E).left x) =
      genericComponentCoordinates T E x :=
  (genericLift_exists T E).choose_spec.2 x

private theorem genericToExplicit_isIso (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : IsIso (genericToExplicit T E) := by
  let g := (genericToExplicit T E).left
  have hg := MorphismProperty.Over.w (genericToExplicit T E)
  change g ≫ componentStructure T E = _ at hg
  have hgeom := generic_geometry T E
  obtain ⟨h, hf, hr⟩ := hgeom.2.2.2
  have htop : IsIso g.base := by
    apply (TopCat.isIso_iff_isHomeomorph _).mpr
    have he : (fun x ↦ g x) = (h.trans (componentFiberHomeo T E).symm) := by
      funext x
      apply (componentFiberHomeo T E).injective
      rw [Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext ((componentFiberHomeo_fst T E _).trans
        ((congrArg (fun f ↦ f x) hg).trans (hf x).symm))
        ((componentFiberHomeo_snd T E _).trans
          ((genericToExplicit_coordinates T E x).trans (hr x).symm))
    change IsHomeomorph (fun x ↦ g x)
    exact he ▸ (h.trans (componentFiberHomeo T E).symm).isHomeomorph
  have : IsIso g := (isIso_iff_isIso_stalkMap g).mpr ⟨htop, fun x ↦ by
    have : IsIso ((componentStructure T E).stalkMap (g x)) :=
      componentStructure_stalk T E (g x)
    have : IsIso ((g ≫ componentStructure T E).stalkMap x) := by
      rw [hg]
      exact hgeom.2.2.1 x
    rw [Scheme.Hom.stalkMap_comp] at this
    exact (isIso_comp_left_iff ((componentStructure T E).stalkMap (g x))
      (g.stalkMap x)).mp this⟩
  let e : (genericComponentFunctor T).obj E ≅ (componentFunctor T).obj E :=
    MorphismProperty.Over.isoMk (asIso g) hg
  change IsIso e.hom
  infer_instance

@[irreducible]
private noncomputable def genericExplicitIso (T : Scheme.{u}) [IsAffine T] :
    genericComponentFunctor T ≅ componentFunctor T := by
  have hn := (affine_component_site_projection T).choose_spec.choose_spec.2.1
  have : ∀ E, IsIso (genericToExplicit T E) := genericToExplicit_isIso T
  refine NatIso.ofComponents (fun E ↦ asIso (genericToExplicit T E)) ?_
  intro E E' a
  apply MorphismProperty.Over.Hom.ext
  apply component_scheme_ext E'
  · exact (MorphismProperty.Over.w
        ((genericComponentFunctor T).map a ≫ genericToExplicit T E')).trans
      (MorphismProperty.Over.w
        (genericToExplicit T E ≫ (componentFunctor T).map a)).symm
  · intro x
    change componentProjection T E'
      ((genericToExplicit T E').left (((genericComponentFunctor T).map a).left x)) =
        componentProjection T E' (((componentFunctor T).map a).left
          ((genericToExplicit T E).left x))
    change componentProjection T E'
      ((genericToExplicit T E').left (((genericComponentFunctor T).map a).left x)) =
        componentProjection T E' ((componentProEtMap a).left
          ((genericToExplicit T E).left x))
    rw [genericToExplicit_coordinates, componentProEtMap_projection,
      genericToExplicit_coordinates]
    unfold genericComponentFunctor at x ⊢
    exact hn E E' a x

private noncomputable def componentMap {T V : Scheme.{u}} [IsAffine T] [IsAffine V]
    (f : V ⟶ T) : componentProfinite V ⟶ componentProfinite T :=
  ConcreteCategory.ofHom ⟨f.continuous.connectedComponentsMap,
    f.continuous.connectedComponentsMap_continuous⟩

private noncomputable def profinitePullbackLift {A B C : Profinite.{u}}
    (a : A ⟶ C) (b : B ⟶ C) {W : Type u} [TopologicalSpace W]
    (x : C(W, A)) (y : C(W, B)) (h : ∀ w, a (x w) = b (y w)) :
    C(W, (pullback a b : Profinite.{u})) := by
  let e := (CompHausLike.pullback.isLimit a b).conePointUniqueUpToIso
    (pullback.isLimit a b)
  exact e.hom.hom.hom.comp
    ⟨fun w ↦ ⟨(x w, y w), h w⟩,
      (x.continuous.prodMk y.continuous).subtype_mk _⟩

private theorem profinitePullbackLift_fst {A B C : Profinite.{u}}
    (a : A ⟶ C) (b : B ⟶ C) {W : Type u} [TopologicalSpace W]
    (x : C(W, A)) (y : C(W, B)) (h : ∀ w, a (x w) = b (y w)) (w : W) :
    pullback.fst a b (profinitePullbackLift a b x y h w) = x w := by
  have he := (CompHausLike.pullback.isLimit a b).conePointUniqueUpToIso_hom_comp
    (pullback.isLimit a b) WalkingCospan.left
  exact ConcreteCategory.congr_hom he ⟨(x w, y w), h w⟩

private theorem profinitePullbackLift_snd {A B C : Profinite.{u}}
    (a : A ⟶ C) (b : B ⟶ C) {W : Type u} [TopologicalSpace W]
    (x : C(W, A)) (y : C(W, B)) (h : ∀ w, a (x w) = b (y w)) (w : W) :
    pullback.snd a b (profinitePullbackLift a b x y h w) = y w := by
  have he := (CompHausLike.pullback.isLimit a b).conePointUniqueUpToIso_hom_comp
    (pullback.isLimit a b) WalkingCospan.right
  exact ConcreteCategory.congr_hom he ⟨(x w, y w), h w⟩

private theorem componentProjection_condition (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (x : componentScheme T E) :
    ConnectedComponents.mk (componentStructure T E x) = E.hom (componentProjection T E x) := by
  have h := (componentFiberHomeo T E x).property
  change ConnectedComponents.mk (componentFiberHomeo T E x).val.1 =
    E.hom (componentFiberHomeo T E x).val.2 at h
  rwa [componentFiberHomeo_fst, componentFiberHomeo_snd] at h

private theorem componentBaseChangeMap_exists {T V : Scheme.{u}} [IsAffine T] [IsAffine V]
    (f : V ⟶ T) (E : Over (componentProfinite T)) :
    let P := (Over.pullback (componentMap f)).obj E
    ∃ g : componentScheme V P ⟶ componentScheme T E,
      g ≫ componentStructure T E = componentStructure V P ≫ f ∧
      ∀ x, componentProjection T E (g x) =
        pullback.fst E.hom (componentMap f) (componentProjection V P x) := by
  dsimp only
  apply component_scheme_lift (T := T)
    (componentStructure V ((Over.pullback (componentMap f)).obj E) ≫ f) E
    ((pullback.fst E.hom (componentMap f)).hom.hom.comp
      (componentProjection V ((Over.pullback (componentMap f)).obj E)))
  intro x
  change ConnectedComponents.mk (f (componentStructure V _ x)) = _
  have hc := componentProjection_condition V
    ((Over.pullback (componentMap f)).obj E) x
  have hp := ConcreteCategory.congr_hom (pullback.condition (f := E.hom)
    (g := componentMap f)) (componentProjection V _ x)
  change E.hom (pullback.fst E.hom (componentMap f) _) =
    componentMap f (pullback.snd E.hom (componentMap f) _) at hp
  change ConnectedComponents.mk (componentStructure V _ x) =
    pullback.snd E.hom (componentMap f) (componentProjection V _ x) at hc
  change componentMap f (ConnectedComponents.mk (componentStructure V _ x)) =
    E.hom (pullback.fst E.hom (componentMap f) (componentProjection V _ x))
  exact (congrArg (fun z ↦ componentMap f z) hc).trans hp.symm

private noncomputable def componentBaseChangeMap {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) (E : Over (componentProfinite T)) :=
  (componentBaseChangeMap_exists f E).choose

private theorem componentBaseChangeMap_base {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) (E : Over (componentProfinite T)) :
    componentBaseChangeMap f E ≫ componentStructure T E =
      componentStructure V ((Over.pullback (componentMap f)).obj E) ≫ f :=
  (componentBaseChangeMap_exists f E).choose_spec.1

private theorem componentBaseChangeMap_coord {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) (E : Over (componentProfinite T))
    (x : componentScheme V ((Over.pullback (componentMap f)).obj E)) :
    componentProjection T E (componentBaseChangeMap f E x) =
      pullback.fst E.hom (componentMap f) (componentProjection V _ x) :=
  (componentBaseChangeMap_exists f E).choose_spec.2 x

private theorem componentBaseChange_isPullback {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) (E : Over (componentProfinite T)) :
    IsPullback (componentBaseChangeMap f E)
      (componentStructure V ((Over.pullback (componentMap f)).obj E))
      (componentStructure T E) f := by
  let P := (Over.pullback (componentMap f)).obj E
  let a := componentBaseChangeMap f E
  let b := componentStructure V P
  have hab : a ≫ componentStructure T E = b ≫ f := componentBaseChangeMap_base f E
  apply IsPullback.of_isLimit (c := PullbackCone.mk a b hab)
  let x (c : PullbackCone (componentStructure T E) f) :=
    (componentProjection T E).comp ⟨c.fst, c.fst.continuous⟩
  let y (c : PullbackCone (componentStructure T E) f) : C(c.pt, componentProfinite V) :=
    ⟨fun w ↦ ConnectedComponents.mk (c.snd w),
      ConnectedComponents.continuous_coe.comp c.snd.continuous⟩
  have hc (c : PullbackCone (componentStructure T E) f) :
      ∀ w, E.hom (x c w) = componentMap f (y c w) := by
    intro w
    change E.hom (componentProjection T E (c.fst w)) =
      ConnectedComponents.mk (f (c.snd w))
    rw [← componentProjection_condition]
    exact congrArg ConnectedComponents.mk (congrArg (fun g ↦ g w) c.condition)
  let r (c : PullbackCone (componentStructure T E) f) :=
    profinitePullbackLift E.hom (componentMap f) (x c) (y c) (hc c)
  have hr (c : PullbackCone (componentStructure T E) f) :
      ∀ w, ConnectedComponents.mk (c.snd w) = P.hom (r c w) := by
    intro w
    exact (profinitePullbackLift_snd E.hom (componentMap f) (x c) (y c) (hc c) w).symm
  let l (c : PullbackCone (componentStructure T E) f) :=
    (component_scheme_lift (T := V) c.snd P (r c) (hr c)).choose
  have lb (c : PullbackCone (componentStructure T E) f) : l c ≫ b = c.snd :=
    (component_scheme_lift (T := V) c.snd P (r c) (hr c)).choose_spec.1
  have lr (c : PullbackCone (componentStructure T E) f) (w : c.pt) :
      componentProjection V P (l c w) = r c w :=
    (component_scheme_lift (T := V) c.snd P (r c) (hr c)).choose_spec.2 w
  have la (c : PullbackCone (componentStructure T E) f) : l c ≫ a = c.fst := by
    apply component_scheme_ext E
    · rw [Category.assoc, componentBaseChangeMap_base, ← Category.assoc, lb]
      exact c.condition.symm
    · intro w
      change componentProjection T E (a (l c w)) = componentProjection T E (c.fst w)
      rw [componentBaseChangeMap_coord, lr]
      exact profinitePullbackLift_fst _ _ _ _ _ w
  refine PullbackCone.IsLimit.mk hab l la lb ?_
  intro c m hm₁ hm₂
  apply component_scheme_ext P
  · exact hm₂.trans (lb c).symm
  · intro w
    have he :
        (ConcreteCategory.ofHom (ContinuousMap.const _ (componentProjection V P (m w))) :
          Profinite.of PUnit.{u + 1} ⟶ P.left) =
        (ConcreteCategory.ofHom (ContinuousMap.const _ (componentProjection V P (l c w))) :
          Profinite.of PUnit.{u + 1} ⟶ P.left) := by
      apply pullback.hom_ext
      · apply ConcreteCategory.hom_ext
        intro z
        change pullback.fst E.hom (componentMap f) (componentProjection V P (m w)) = _
        change pullback.fst E.hom (componentMap f) (componentProjection V P (m w)) =
          pullback.fst E.hom (componentMap f) (componentProjection V P (l c w))
        rw [← componentBaseChangeMap_coord, ← componentBaseChangeMap_coord]
        exact congrArg (fun g ↦ componentProjection T E (g w))
          (hm₁.trans (la c).symm)
      · apply ConcreteCategory.hom_ext
        intro z
        change P.hom (componentProjection V P (m w)) =
          P.hom (componentProjection V P (l c w))
        rw [← componentProjection_condition, ← componentProjection_condition]
        exact congrArg ConnectedComponents.mk
          ((congrArg (fun g ↦ g w) hm₂).trans (congrArg (fun g ↦ g w) (lb c)).symm)
    exact ConcreteCategory.congr_hom he PUnit.unit

private theorem componentBaseChangeMap_natural {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T)
    {E E' : Over (componentProfinite T)} (a : E ⟶ E') :
    ((componentFunctor V).map ((Over.pullback (componentMap f)).map a)).left ≫
        componentBaseChangeMap f E' =
      componentBaseChangeMap f E ≫ ((componentFunctor T).map a).left := by
  let b := ((componentFunctor V).map ((Over.pullback (componentMap f)).map a)).left
  apply component_scheme_ext E'
  · have hb := MorphismProperty.Over.w
      ((componentFunctor V).map ((Over.pullback (componentMap f)).map a))
    have ha := MorphismProperty.Over.w ((componentFunctor T).map a)
    change b ≫ componentStructure V ((Over.pullback (componentMap f)).obj E') =
      componentStructure V ((Over.pullback (componentMap f)).obj E) at hb
    change ((componentFunctor T).map a).left ≫ componentStructure T E' =
      componentStructure T E at ha
    rw [Category.assoc, componentBaseChangeMap_base, ← Category.assoc, hb,
      Category.assoc, ha, componentBaseChangeMap_base]
  · intro x
    change componentProjection T E' (componentBaseChangeMap f E' (b x)) =
      componentProjection T E' ((componentProEtMap a).left (componentBaseChangeMap f E x))
    rw [componentBaseChangeMap_coord, componentProEtMap_projection,
      componentBaseChangeMap_coord]
    change pullback.fst E'.hom (componentMap f)
      (componentProjection V _ ((componentProEtMap
        ((Over.pullback (componentMap f)).map a)).left x)) = _
    rw [componentProEtMap_projection]
    change pullback.fst E'.hom (componentMap f)
      (pullback.lift (pullback.fst E.hom (componentMap f) ≫ a.left)
        (pullback.snd E.hom (componentMap f)) _ (componentProjection V _ x)) = _
    exact ConcreteCategory.congr_hom
      (pullback.lift_fst (pullback.fst E.hom (componentMap f) ≫ a.left)
        (pullback.snd E.hom (componentMap f)) _) (componentProjection V _ x)

@[irreducible]
private noncomputable def componentBaseChangeIso {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) :
    Over.pullback (componentMap f) ⋙ componentFunctor V ≅
      componentFunctor T ⋙ Scheme.proEtaleBaseChange f := by
  let e (E : Over (componentProfinite T)) :
      (Over.pullback (componentMap f) ⋙ componentFunctor V).obj E ≅
        (componentFunctor T ⋙ Scheme.proEtaleBaseChange f).obj E :=
    MorphismProperty.Over.isoMk (componentBaseChange_isPullback f E).isoPullback
      (componentBaseChange_isPullback f E).isoPullback_hom_snd
  have he₁ (E : Over (componentProfinite T)) :
      (e E).hom.left ≫ pullback.fst ((componentFunctor T).obj E).hom f =
        componentBaseChangeMap f E :=
    (componentBaseChange_isPullback f E).isoPullback_hom_fst
  have he₂ (E : Over (componentProfinite T)) :
      (e E).hom.left ≫ pullback.snd ((componentFunctor T).obj E).hom f =
        componentStructure V ((Over.pullback (componentMap f)).obj E) :=
    (componentBaseChange_isPullback f E).isoPullback_hom_snd
  refine NatIso.ofComponents e ?_
  intro E E' a
  apply MorphismProperty.Over.Hom.ext
  change ((componentFunctor V).map ((Over.pullback (componentMap f)).map a)).left ≫
      (e E').hom.left = (e E).hom.left ≫ ((Scheme.proEtaleBaseChange f).map
        ((componentFunctor T).map a)).left
  apply pullback.hom_ext
  · rw [Category.assoc, he₁, Category.assoc,
      MorphismProperty.Over.pullback_map_left, pullback.lift_fst, ← Category.assoc, he₁]
    exact componentBaseChangeMap_natural f a
  · rw [Category.assoc, he₂, Category.assoc,
      MorphismProperty.Over.pullback_map_left, pullback.lift_snd, he₂]
    exact MorphismProperty.Over.w
      ((componentFunctor V).map ((Over.pullback (componentMap f)).map a))

private theorem componentComponentsHomeo_mk (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (x : componentScheme T E) :
    componentComponentsHomeo T E (ConnectedComponents.mk x) = componentProjection T E x := rfl

attribute [local irreducible] componentComponentsHomeo

private theorem componentFunctor_fullyFaithful (T : Scheme.{u}) [IsAffine T] :
    (componentFunctor T).Full ∧ (componentFunctor T).Faithful := by
  have hinj {E E' : Over (componentProfinite T)} (a b : E ⟶ E')
      (h : (componentFunctor T).map a = (componentFunctor T).map b) : a = b := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro e
    obtain ⟨x, rfl⟩ := componentProjection_surjective T E e
    rw [← componentProEtMap_projection, ← componentProEtMap_projection]
    exact congrArg (fun k ↦ componentProjection T E' (k.left x)) h
  have hsurj {E E' : Over (componentProfinite T)}
      (a : (componentFunctor T).obj E ⟶ (componentFunctor T).obj E') :
      ∃ b : E ⟶ E', (componentFunctor T).map b = a := by
    let r : C(componentScheme T E, E'.left) :=
      (componentProjection T E').comp ⟨a.left, a.left.continuous⟩
    let q : C(E.left, E'.left) :=
      (⟨r.continuous.connectedComponentsLift,
        r.continuous.connectedComponentsLift_continuous⟩ :
          C(ConnectedComponents (componentScheme T E), E'.left)).comp
            ⟨(componentComponentsHomeo T E).symm,
              (componentComponentsHomeo T E).symm.continuous⟩
    have hq (x : componentScheme T E) : q (componentProjection T E x) =
        componentProjection T E' (a.left x) := by
      rw [← componentComponentsHomeo_mk]
      change r.continuous.connectedComponentsLift
        ((componentComponentsHomeo T E).symm
          (componentComponentsHomeo T E (ConnectedComponents.mk x))) = _
      rw [Homeomorph.symm_apply_apply]
      rfl
    have hw : ConcreteCategory.ofHom q ≫ E'.hom = E.hom := by
      apply ConcreteCategory.hom_ext
      intro e
      obtain ⟨x, rfl⟩ := componentProjection_surjective T E e
      change E'.hom (q (componentProjection T E x)) = E.hom (componentProjection T E x)
      rw [hq, ← componentProjection_condition, ← componentProjection_condition]
      exact congrArg ConnectedComponents.mk (congrArg (fun k ↦ k x) a.w)
    refine ⟨Over.homMk (ConcreteCategory.ofHom q) hw, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    apply component_scheme_ext E'
    · have hb := ((componentFunctor T).map
          (Over.homMk (ConcreteCategory.ofHom q) hw)).w
      change ((componentFunctor T).map
        (Over.homMk (ConcreteCategory.ofHom q) hw)).left ≫ componentStructure T E' =
          componentStructure T E at hb
      have ha := a.w
      change a.left ≫ componentStructure T E' = componentStructure T E at ha
      exact hb.trans ha.symm
    · intro x
      exact (componentProEtMap_projection _ x).trans (hq x)
  exact ⟨⟨fun a ↦ hsurj a⟩, ⟨fun h ↦ hinj _ _ h⟩⟩

private theorem field_affine_totallyDisconnected (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (V : (Spec (.of Ω)).ProEt) [IsAffine V.left] : TotallyDisconnectedSpace V.left := by
  obtain ⟨S, ⟨e⟩⟩ := AlgebraicGeometry.ProEtale.affineClassification Ω V
  exact ((AlgebraicGeometry.ProEtale.testSpaceHomeo Ω S).trans
    (Scheme.homeoOfIso
      { hom := e.inv.left
        inv := e.hom.left
        hom_inv_id := congrArg (fun f ↦ f.left) e.inv_hom_id
        inv_hom_id := congrArg (fun f ↦ f.left) e.hom_inv_id })).totallyDisconnectedSpace

private theorem field_affine_stalks (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (V : (Spec (.of Ω)).ProEt) [IsAffine V.left] (x : V.left) :
    IsIso (V.hom.stalkMap x) := by
  let R := Γ(V.left, ⊤)
  let φ : CommRingCat.of Ω ⟶ R := Spec.preimage (V.left.isoSpec.inv ≫ V.hom)
  let : Algebra Ω R := φ.hom.toAlgebra
  have hφ : Spec.map φ = V.left.isoSpec.inv ≫ V.hom := Spec.map_preimage _
  have : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap Ω R))) := by
    change WeaklyEtale (Spec.map φ)
    rw [hφ]
    infer_instance
  have : Algebra.WeaklyEtale Ω R := weaklyEtale_SpecMap_algebraMap_iff.mp this
  have : Algebra.BijectiveOnStalks Ω R := stalks Ω R
  have hb (p : PrimeSpectrum R) : IsIso (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap φ.hom p).asIdeal p.asIdeal φ.hom rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Algebra.BijectiveOnStalks.bijective_localRingHom (R := Ω) p.asIdeal)
  have hi : IsIso ((Spec.map φ).stalkMap (V.left.isoSpec.hom x)) := by
    rw [← Scheme.localRingHom_comp_stalkIso]
    infer_instance
  rw [hφ, Scheme.Hom.stalkMap_comp] at hi
  have h := (isIso_comp_right_iff (V.hom.stalkMap (V.left.isoSpec.inv
    (V.left.isoSpec.hom x))) (V.left.isoSpec.inv.stalkMap (V.left.isoSpec.hom x))).mp hi
  have hx : V.left.isoSpec.inv (V.left.isoSpec.hom x) = x :=
    congrArg (fun f : V.left ⟶ V.left ↦ f x) V.left.isoSpec.hom_inv_id
  exact hx ▸ h

private noncomputable def disconnectedComponentHomeo (T : Scheme.{u}) [IsAffine T]
    [TotallyDisconnectedSpace T] (E : Over (componentProfinite T)) :
    componentScheme T E ≃ₜ E.left := by
  let e := ConnectedComponents.mkHomeomorph (S := T)
  let k : {p : T × E.left | ConnectedComponents.mk p.1 = E.hom p.2} ≃ₜ E.left :=
    { toFun := fun p ↦ p.val.2
      invFun := fun x ↦ ⟨(e.symm (E.hom x), x), e.apply_symm_apply _⟩
      left_inv := fun p ↦ by
        apply Subtype.ext
        exact Prod.ext (e.symm_apply_eq.mpr p.property.symm) rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_snd.comp continuous_subtype_val
      continuous_invFun := ((e.symm.continuous.comp E.hom.hom.hom.continuous).prodMk
        continuous_id).subtype_mk _ }
  exact (componentFiberHomeo T E).trans k

private theorem field_affine_component_iso (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (T : (Spec (.of Ω)).ProEt) [IsAffine T.left]
    (W : T.left.ProEt) [IsAffine W.left] :
    ∃ E : Over (componentProfinite T.left), Nonempty (W ≅ (componentFunctor T.left).obj E) := by
  let Z : (Spec (.of Ω)).ProEt := ProEt.mk (W.hom ≫ T.hom)
  have : IsAffine Z.left := inferInstanceAs (IsAffine W.left)
  have : TotallyDisconnectedSpace T.left := field_affine_totallyDisconnected Ω T
  have : TotallyDisconnectedSpace W.left := field_affine_totallyDisconnected Ω Z
  let E : Over (componentProfinite T.left) :=
    Over.mk (componentMap (T := T.left) (V := W.left) W.hom)
  let r : C(W.left, E.left) := ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  obtain ⟨g, hg, hr⟩ := component_scheme_lift (T := T.left) (W := W.left) W.hom E r (by
    intro x
    change ConnectedComponents.mk (W.hom x) =
      W.hom.continuous.connectedComponentsMap (ConnectedComponents.mk x)
    exact (W.hom.continuous.connectedComponentsMap_mk x).symm)
  have hi : IsIso g := by
    apply (isIso_iff_isIso_stalkMap g).mpr
    constructor
    · apply (TopCat.isIso_iff_isHomeomorph _).mpr
      let e := (ConnectedComponents.mkHomeomorph (S := W.left)).trans
        (disconnectedComponentHomeo T.left E).symm
      have he : (fun x ↦ g x) = e := by
        funext x
        apply (disconnectedComponentHomeo T.left E).injective
        rw [show disconnectedComponentHomeo T.left E (g x) =
          componentProjection T.left E (g x) from componentFiberHomeo_snd T.left E _, hr]
        exact ((disconnectedComponentHomeo T.left E).apply_symm_apply _).symm
      change IsHomeomorph (fun x ↦ g x)
      exact he ▸ e.isHomeomorph
    · intro x
      have hT : IsIso (T.hom.stalkMap (W.hom x)) := field_affine_stalks Ω T _
      have hZ : IsIso ((W.hom ≫ T.hom).stalkMap x) := field_affine_stalks Ω Z x
      rw [Scheme.Hom.stalkMap_comp] at hZ
      have hW : IsIso (W.hom.stalkMap x) := (isIso_comp_left_iff _ _).mp hZ
      have hcomp : IsIso ((g ≫ componentStructure T.left E).stalkMap x) := hg ▸ hW
      rw [Scheme.Hom.stalkMap_comp] at hcomp
      have := componentStructure_stalk T.left E (g x)
      exact (isIso_comp_left_iff _ _).mp hcomp
  exact ⟨E, ⟨MorphismProperty.Over.isoMk (asIso g) hg⟩⟩

private theorem componentTopologyReflect (T : Scheme.{u}) [IsAffine T]
    {E : Over (componentProfinite T)} {R : Sieve E}
    (hR : R.functorPushforward (componentFunctor T) ∈ topology T _) :
    R ∈ (coherentTopology Profinite.{u}).over (componentProfinite T) E := by
  let W : Qcqs T := ⟨(componentFunctor T).obj E,
    inferInstanceAs (CompactSpace (componentScheme T E)),
    inferInstanceAs (QuasiSeparatedSpace (componentScheme T E))⟩
  obtain ⟨n, V, f, hf, hmem⟩ := component_finite_refinement T W
    (R.functorPushforward (componentFunctor T)) hR
  choose S a b ha hfac using hmem
  rw [GrothendieckTopology.mem_over_iff]
  apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mpr
  refine ⟨Fin n, inferInstance, fun i ↦ (S i).left, fun i ↦ (a i).left, ?_, ?_⟩
  · apply ((Profinite.effectiveEpiFamily_tfae _ _).out 0 2).mpr
    have hsurj : ∀ x : componentScheme T E,
        ∃ i y, (f i).left y = x := by
      have h := Scheme.ProEt.mem_precoverage_iff.mp hf
      rw [Presieve.map_ofArrows] at h
      have h' := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
        inf_le_right) _ h
      intro x
      obtain ⟨Y, g, hg, y, hy⟩ := h'.1 x
      obtain ⟨hg⟩ := hg
      obtain ⟨i⟩ := hg
      exact ⟨i, y, hy⟩
    intro e
    obtain ⟨x, hx⟩ := componentProjection_surjective T E e
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨i, componentProjection T (S i) ((b i).left y), ?_⟩
    rw [← componentProEtMap_projection]
    have he := congrArg (fun k ↦ componentProjection T E (k.left y)) (hfac i)
    change componentProjection T E ((f i).left y) =
      componentProjection T E (((componentFunctor T).map (a i)).left ((b i).left y)) at he
    exact he.symm.trans ((congrArg (componentProjection T E) hy).trans hx)
  · intro i
    exact ⟨S i, a i, 𝟙 _, ha i, by simp⟩

private theorem field_component_dense (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (T : (Spec (.of Ω)).ProEt) [IsAffine T.left] :
    (componentFunctor T.left).IsDenseSubsite
      ((coherentTopology Profinite.{u}).over (componentProfinite T.left))
      (topology T.left) := by
  have := (componentFunctor_fullyFaithful T.left).1
  have := (componentFunctor_fullyFaithful T.left).2
  have : (componentFunctor T.left).IsCoverDense (topology T.left) := by
    constructor
    intro U
    apply (topology T.left).superset_covering _
      ((Scheme.AffineProEt.toProEt T.left).is_cover_of_isCoverDense _ U)
    rintro W f ⟨⟨A, g, h, w⟩⟩
    let Z := (Scheme.AffineProEt.toProEt T.left).obj A
    have : IsAffine Z.left := inferInstanceAs (IsAffine A.left)
    obtain ⟨E, ⟨e⟩⟩ := field_affine_component_iso Ω T Z
    exact ⟨⟨E, g ≫ e.hom, e.inv ≫ h, by simp [Category.assoc, w]⟩⟩
  exact { functorPushforward_mem_iff := fun {_ _} ↦
    ⟨componentTopologyReflect T.left, (component_coverPreserving T.left).cover_preserve⟩ }

attribute [local instance] component_continuous

@[irreducible]
private noncomputable def genericRestrictionIso (T : Scheme.{u}) [IsAffine T] :
    (genericComponentProjection T).direct ≅
      (genericComponentFunctor T).sheafPushforwardContinuous (Type (u + 1))
        ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) := by
  unfold genericComponentProjection genericComponentFunctor
  exact ((affine_component_site_projection T).choose_spec.choose_spec.2.2.2.2).choose_spec.1
    |>.choose_spec.choose

private noncomputable def genericDirectIso (T : Scheme.{u}) [IsAffine T] :
    (genericComponentProjection T).direct ≅
      (componentFunctor T).sheafPushforwardContinuous (Type (u + 1))
        ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) := by
  have : (componentFunctor T).IsContinuous
      ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) :=
    component_continuous T
  exact genericRestrictionIso T ≪≫
      Functor.sheafPushforwardContinuousIso (genericExplicitIso T)
        (Type (u + 1)) _ _

private theorem field_generic_equivalence (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (T : (Spec (.of Ω)).ProEt) [IsAffine T.left] :
    (genericComponentProjection T.left).inverse.IsEquivalence := by
  have := field_component_dense Ω T
  have : ((componentFunctor T.left).sheafPushforwardContinuous (Type (u + 1))
      ((coherentTopology Profinite.{u}).over (componentProfinite T.left))
      (topology T.left)).IsEquivalence := inferInstance
  have := Functor.isEquivalence_of_iso (genericDirectIso T.left).symm
  exact (genericComponentProjection T.left).adj.isEquivalence_left_of_isEquivalence_right

@[irreducible]
private noncomputable def genericBaseChangeIso {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) :
    Over.pullback (componentMap f) ⋙ genericComponentFunctor V ≅
      genericComponentFunctor T ⋙ Scheme.proEtaleBaseChange f :=
  Functor.isoWhiskerLeft _ (genericExplicitIso V) ≪≫ componentBaseChangeIso f ≪≫
    Functor.isoWhiskerRight (genericExplicitIso T).symm _

private noncomputable def genericBaseChangeInverseIso {T V : Scheme.{u}}
    [IsAffine T] [IsAffine V] (f : V ⟶ T) :
    (coherentTopology Profinite.{u}).overMapPullback (Type (u + 1)) (componentMap f) ⋙
      (genericComponentProjection V).inverse ≅
        (genericComponentProjection T).inverse ⋙
          Scheme.proEtaleSheafInverseImage f (Type (u + 1)) := by
  let J := coherentTopology Profinite.{u}
  have : (Over.pullback (componentMap f)).IsContinuous
      (J.over (componentProfinite T)) (J.over (componentProfinite V)) := inferInstance
  let a := (Over.mapPullbackAdj (componentMap f)).sheafPushforwardContinuous
    (E := Type (u + 1)) (J.over (componentProfinite V)) (J.over (componentProfinite T))
  let gT := genericComponentProjection T
  let gV := genericComponentProjection V
  let rT := genericRestrictionIso T
  let rV := genericRestrictionIso V
  have := Functor.isContinuous_comp (genericComponentFunctor T)
    (Scheme.proEtaleBaseChange f) (J.over (componentProfinite T)) (topology T) (topology V)
  let e := Functor.isoWhiskerRight rV _ ≪≫
    Functor.sheafPushforwardContinuousComp' (eFG := genericBaseChangeIso f)
      (Type (u + 1)) (J.over (componentProfinite T)) (J.over (componentProfinite V)) (topology V) ≪≫
    ((genericComponentFunctor T).sheafPushforwardContinuousComp
      (Scheme.proEtaleBaseChange f) (Type (u + 1))
      (J.over (componentProfinite T)) (topology T) (topology V)).symm ≪≫
    Functor.isoWhiskerLeft _ rT.symm
  exact (conjugateIsoEquiv (a.comp gV.adj)
    (gT.adj.comp (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))).symm e |>.symm

private theorem test_isAffine (T : Scheme.{u}) [IsAffine T] (S : Profinite.{u}) :
    IsAffine ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left := by
  change IsAffine (pullback
    (AlgebraicGeometry.ProEtale.toSpecZ (AlgebraicGeometry.ProEtale.profiniteToScheme.obj S))
    (AlgebraicGeometry.ProEtale.toSpecZ T))
  have : IsAffine (AlgebraicGeometry.ProEtale.profiniteToScheme.obj S) := by
    change IsAffine (Spec _)
    infer_instance
  have : IsAffineHom (AlgebraicGeometry.ProEtale.toSpecZ T) := isAffineHom_of_isAffine _
  infer_instance

private noncomputable def testComponents (T : Scheme.{u}) [IsAffine T] (S : Profinite.{u}) :
    Profinite.{u} := by
  have := test_isAffine T S
  exact componentProfinite ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left

private noncomputable def testLabelsOnComponents (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) : testComponents T S ⟶ S :=
  ConcreteCategory.ofHom
    ⟨(AlgebraicGeometry.ProEtale.label T S).continuous.connectedComponentsLift,
      (AlgebraicGeometry.ProEtale.label T S).continuous.connectedComponentsLift_continuous⟩

private noncomputable def testComponentCoordinate (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) :
    C(((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left,
      ((Over.star (componentProfinite T)).obj S).left) := by
  have := test_isAffine T S
  let p : testComponents T S ⟶ componentProfinite T ⨯ S :=
    prod.lift (@componentMap T ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left
      inferInstance (test_isAffine T S)
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom)
      (testLabelsOnComponents T S)
  exact p.hom.hom.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩

private theorem testComponentCoordinate_fst (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) (x : ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left) :
    (prod.fst : componentProfinite T ⨯ S ⟶ componentProfinite T)
      (testComponentCoordinate T S x) =
      ConnectedComponents.mk (((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom x) := by
  have := test_isAffine T S
  exact ConcreteCategory.congr_hom (prod.lift_fst
    (@componentMap T ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left
      inferInstance (test_isAffine T S)
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom)
    (testLabelsOnComponents T S)) (ConnectedComponents.mk x)

private theorem testComponentCoordinate_snd (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) (x : ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left) :
    (prod.snd : componentProfinite T ⨯ S ⟶ S) (testComponentCoordinate T S x) =
        AlgebraicGeometry.ProEtale.label T S x := by
  have := test_isAffine T S
  exact ConcreteCategory.congr_hom (prod.lift_snd
    (@componentMap T ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left
      inferInstance (test_isAffine T S)
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom)
    (testLabelsOnComponents T S)) (ConnectedComponents.mk x)

private theorem star_hom (Q S : Profinite.{u}) :
    ((Over.star Q).obj S).hom = (prod.fst : Q ⨯ S ⟶ Q) :=
  (Over.star_obj_hom Q S).trans (prod.lift_fst _ _)

private theorem absoluteToComponent_exists (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) :
    ∃ g : ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left ⟶
        componentScheme T ((Over.star (componentProfinite T)).obj S),
      g ≫ componentStructure T ((Over.star (componentProfinite T)).obj S) =
          ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom ∧
      ∀ x, componentProjection T _ (g x) = testComponentCoordinate T S x := by
  exact component_scheme_lift (T := T)
    ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom
      ((Over.star (componentProfinite T)).obj S) (testComponentCoordinate T S)
        (fun x ↦ (testComponentCoordinate_fst T S x).symm.trans
          (congrArg (fun f : componentProfinite T ⨯ S ⟶ componentProfinite T ↦
            f (testComponentCoordinate T S x)) (star_hom _ _).symm))

private noncomputable def absoluteToComponent (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) :
    (AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S ⟶
      (componentFunctor T).obj ((Over.star (componentProfinite T)).obj S) :=
  MorphismProperty.Over.homMk (absoluteToComponent_exists T S).choose
    (absoluteToComponent_exists T S).choose_spec.1

private theorem componentToAbsolute_exists (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) :
    ∃ g : componentScheme T ((Over.star (componentProfinite T)).obj S) ⟶
        ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left,
      g ≫ ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom =
          componentStructure T ((Over.star (componentProfinite T)).obj S) ∧
      ∀ x, AlgebraicGeometry.ProEtale.label T S (g x) =
        (prod.snd : componentProfinite T ⨯ S ⟶ S) (componentProjection T _ x) := by
  obtain ⟨g, hg⟩ := (AlgebraicGeometry.ProEtale.label_bijective T
    (componentScheme T ((Over.star (componentProfinite T)).obj S))
    (componentStructure T ((Over.star (componentProfinite T)).obj S)) S).surjective
      ((prod.snd : componentProfinite T ⨯ S ⟶ S).hom.hom.comp (componentProjection T _))
  exact ⟨g.left, g.w, fun x ↦ ContinuousMap.congr_fun hg x⟩

private noncomputable def componentToAbsolute (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) :
    (componentFunctor T).obj ((Over.star (componentProfinite T)).obj S) ⟶
      (AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S :=
  MorphismProperty.Over.homMk (componentToAbsolute_exists T S).choose
    (componentToAbsolute_exists T S).choose_spec.1

private theorem absoluteToComponent_coord (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) (x) :
    componentProjection T _ ((absoluteToComponent T S).left x) =
      testComponentCoordinate T S x := (absoluteToComponent_exists T S).choose_spec.2 x

private theorem componentToAbsolute_coord (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) (x) :
    AlgebraicGeometry.ProEtale.label T S ((componentToAbsolute T S).left x) =
      (prod.snd : componentProfinite T ⨯ S ⟶ S) (componentProjection T _ x) :=
  (componentToAbsolute_exists T S).choose_spec.2 x

private theorem prod_point_ext {A B : Profinite.{u}} {x y : (A ⨯ B : Profinite)}
    (h₁ : (prod.fst : A ⨯ B ⟶ A) x = (prod.fst : A ⨯ B ⟶ A) y)
    (h₂ : (prod.snd : A ⨯ B ⟶ B) x = (prod.snd : A ⨯ B ⟶ B) y) : x = y := by
  have he : (ConcreteCategory.ofHom (ContinuousMap.const PUnit.{u + 1} x) :
      Profinite.of PUnit.{u + 1} ⟶ A ⨯ B) =
      (ConcreteCategory.ofHom (ContinuousMap.const PUnit.{u + 1} y) :
        Profinite.of PUnit.{u + 1} ⟶ A ⨯ B) := by
    apply prod.hom_ext <;> ext z
    · exact h₁
    · exact h₂
  exact ConcreteCategory.congr_hom he PUnit.unit

private theorem absoluteComponent_inverse (T : Scheme.{u}) [IsAffine T]
    (S : Profinite.{u}) :
    absoluteToComponent T S ≫ componentToAbsolute T S = 𝟙 _ ∧
      componentToAbsolute T S ≫ absoluteToComponent T S = 𝟙 _ := by
  have hc := absoluteToComponent_coord T S
  have ha := componentToAbsolute_coord T S
  constructor
  · apply MorphismProperty.Over.Hom.ext
    have := test_isAffine T S
    apply congrArg (fun f : Over.mk
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom ⟶
        (Scheme.ProEt.forget T).obj
          ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S) ↦ f.left)
    apply (AlgebraicGeometry.ProEtale.label_bijective T
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).left
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom S).injective
      (a₁ := Over.homMk ((absoluteToComponent T S ≫ componentToAbsolute T S).left)
        (MorphismProperty.Over.w _)) (a₂ := 𝟙 _)
    ext x
    change AlgebraicGeometry.ProEtale.label T S
      ((componentToAbsolute T S).left ((absoluteToComponent T S).left x)) = _
    rw [ha, hc]
    exact testComponentCoordinate_snd T S x
  · apply MorphismProperty.Over.Hom.ext
    apply component_scheme_ext ((Over.star (componentProfinite T)).obj S)
    · exact MorphismProperty.Over.w _
    · intro x
      change componentProjection T _ ((absoluteToComponent T S).left
        ((componentToAbsolute T S).left x)) = componentProjection T _ x
      rw [hc]
      apply prod_point_ext
      · rw [testComponentCoordinate_fst]
        have h := componentProjection_condition T ((Over.star (componentProfinite T)).obj S) x
        have h' := h.trans (congrArg
          (fun f : componentProfinite T ⨯ S ⟶ componentProfinite T ↦
            f (componentProjection T ((Over.star (componentProfinite T)).obj S) x))
          (star_hom _ _))
        exact (congrArg ConnectedComponents.mk
          (congrArg (fun f ↦ f x) (MorphismProperty.Over.w (componentToAbsolute T S)))).trans h'
      · rw [testComponentCoordinate_snd, ha]

@[irreducible]
private noncomputable def absoluteComponentIso (T : Scheme.{u}) [IsAffine T] :
    AlgebraicGeometry.ProEtale.profiniteToProEtOf T ≅
      Over.star (componentProfinite T) ⋙ componentFunctor T := by
  let e (S : Profinite.{u}) :
      (AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S ≅
        (componentFunctor T).obj ((Over.star (componentProfinite T)).obj S) :=
    { hom := absoluteToComponent T S
      inv := componentToAbsolute T S
      hom_inv_id := (absoluteComponent_inverse T S).1
      inv_hom_id := (absoluteComponent_inverse T S).2 }
  refine NatIso.ofComponents e ?_
  intro S S' a
  apply MorphismProperty.Over.Hom.ext
  apply component_scheme_ext ((Over.star (componentProfinite T)).obj S')
  · exact (MorphismProperty.Over.w
      ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).map a ≫ absoluteToComponent T S')).trans
        (MorphismProperty.Over.w
          (absoluteToComponent T S ≫ (componentFunctor T).map
            ((Over.star (componentProfinite T)).map a))).symm
  · intro x
    change componentProjection T _ ((absoluteToComponent T S').left
        (((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).map a).left x)) =
      componentProjection T _ ((componentProEtMap ((Over.star (componentProfinite T)).map a)).left
        ((absoluteToComponent T S).left x))
    rw [absoluteToComponent_coord, componentProEtMap_projection,
      absoluteToComponent_coord]
    apply prod_point_ext
    · rw [testComponentCoordinate_fst]
      change ConnectedComponents.mk
        (((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S').hom
          (((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).map a).left x)) = _
      rw [show ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S').hom
        (((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).map a).left x) =
          ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).obj S).hom x from
            congrArg (fun f ↦ f x) (MorphismProperty.Over.w
              ((AlgebraicGeometry.ProEtale.profiniteToProEtOf T).map a))]
      have h := ConcreteCategory.congr_hom
        (prod.map_fst (𝟙 (componentProfinite T)) a) (testComponentCoordinate T S x)
      change (prod.fst : componentProfinite T ⨯ S' ⟶ componentProfinite T)
        ((prod.map (𝟙 (componentProfinite T)) a) (testComponentCoordinate T S x)) =
          (prod.fst : componentProfinite T ⨯ S ⟶ componentProfinite T)
            (testComponentCoordinate T S x) at h
      exact (testComponentCoordinate_fst T S x).symm.trans h.symm
    · rw [testComponentCoordinate_snd]
      exact (ContinuousMap.congr_fun
        (AlgebraicGeometry.ProEtale.label_natural T S S' a) x).trans
          (by
            change a (AlgebraicGeometry.ProEtale.label T S x) =
              (prod.snd : componentProfinite T ⨯ S' ⟶ S')
                (prod.map (𝟙 (componentProfinite T)) a (testComponentCoordinate T S x))
            exact (congrArg (fun z ↦ a z) (testComponentCoordinate_snd T S x)).symm.trans
              (ConcreteCategory.congr_hom (prod.map_snd (𝟙 (componentProfinite T)) a)
                (testComponentCoordinate T S x)).symm)

@[irreducible]
private noncomputable def genericAbsoluteIso (T : Scheme.{u}) [IsAffine T] :
    Over.star (componentProfinite T) ⋙ genericComponentFunctor T ≅
      AlgebraicGeometry.ProEtale.profiniteToProEtOf T :=
  Functor.isoWhiskerLeft _ (genericExplicitIso T) ≪≫ (absoluteComponentIso T).symm

private noncomputable def genericAbsoluteInverseIso (T : Scheme.{u}) [IsAffine T] :
    (coherentTopology Profinite.{u}).overPullback (Type (u + 1)) (componentProfinite T) ⋙
      (genericComponentProjection T).inverse ≅
        AlgebraicGeometry.ProEtale.profinitePointSetSchemeInverseImage T := by
  let J := coherentTopology Profinite.{u}
  let a := (Over.forgetAdjStar (componentProfinite T)).sheafPushforwardContinuous
    (E := Type (u + 1)) (J.over (componentProfinite T)) J
  let g := genericComponentProjection T
  let r := genericRestrictionIso T
  let e := Functor.isoWhiskerRight r _ ≪≫
    Functor.sheafPushforwardContinuousComp' (eFG := genericAbsoluteIso T)
      (Type (u + 1)) J (J.over (componentProfinite T)) (topology T)
  exact (conjugateIsoEquiv (a.comp g.adj)
    (AlgebraicGeometry.ProEtale.geometricFieldPointAdjunction T)).symm e |>.symm

/-- The component-site base-change square and its geometric-field equivalence.
Source: HRS, proof of Theorem 4.13, diagram (4.4); Bhatt--Scholze Lemma 2.2.8
(blueprint: lem-zl-generic-component-site-comparison).

Proof: the geometric-field classification makes every affine weakly etale scheme
profinite, with unchanged stalks. The component universal property identifies the
affine basis over V with the profinite slice over its actual component quotient.
The component functor is full and faithful and reflects covers; affine cover density
then gives an equivalence on sheaves, and hence on its left adjoint.
For E over π₀(U), base-changing U_E gives V_(E ×_π₀(U) π₀(V)): the spaces are the same
fibre product and their structure sheaves are inverse images of the same sheaf.
Uniqueness gives naturality, and taking adjunction mates gives the displayed square.
Likewise V ×_Ω Ω[E] = Ω[π₀(V) × E]. The geometric-field point equivalence therefore
identifies the structural inverse image with pullback along π₀(V) → *. No genericity
or w-contractibility is used in these site identities. Empty schemes are included. -/
theorem generic_component_site_comparison
    (X : Scheme.{u}) [IsAffine X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X)
    (U : X.ProEt) [IsAffine U.left]
    (hind : RingHom.IndEtaleAcrossUniverses U.hom.appTop.hom) :
    letI : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    letI : IsAffineHom η := isAffineHom_of_isAffine η
    letI : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let V : Scheme := pullback U.hom η
    let S : Profinite.{u} := Scheme.ProEt.componentProfinite U.left
    let Sη : Profinite.{u} := Scheme.ProEt.componentProfinite V
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    (genericComponentProjection V).inverse.IsEquivalence ∧
      Nonempty ((coherentTopology Profinite.{u}).overMapPullback
          (Type (u + 1)) (ConcreteCategory.ofHom r : Sη ⟶ S) ⋙
        (genericComponentProjection V).inverse ≅
          (genericComponentProjection U.left).inverse ⋙
            Scheme.proEtaleSheafInverseImage (pullback.fst U.hom η) (Type (u + 1))) ∧
      Nonempty ((coherentTopology Profinite.{u}).overPullback (Type (u + 1)) Sη ⋙
          (genericComponentProjection V).inverse ≅
        AlgebraicGeometry.ProEtale.profinitePointSetSchemeInverseImage (Spec (.of Ω)) ⋙
          Scheme.proEtaleSheafInverseImage (pullback.snd U.hom η) (Type (u + 1))) := by
  have _hind := hind
  let : IsAffineHom (show U.left ⟶ X from U.hom) :=
    isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
  let : IsAffineHom η := isAffineHom_of_isAffine η
  let : IsAffine (pullback U.hom η) :=
    instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
  dsimp only
  let V := pullback U.hom η
  let T : (Spec (.of Ω)).ProEt := ProEt.mk (pullback.snd U.hom η)
  have : IsAffine T.left := by
    change IsAffine V
    infer_instance
  refine ⟨field_generic_equivalence Ω T, ⟨genericBaseChangeInverseIso _⟩, ?_⟩
  exact ⟨genericAbsoluteInverseIso V ≪≫
    (AlgebraicGeometry.ProEtale.profinitePointSetSchemeComp (pullback.snd U.hom η)).symm⟩

end AlgebraicGeometry.Scheme.ProEt
