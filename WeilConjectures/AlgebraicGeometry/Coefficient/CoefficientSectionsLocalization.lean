/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization

/-!
# Coefficient sections and localization

Source: Stacks Project, sites.tex, Tags 00Y0 and 03EH; proetale.tex, Tag 098T;
canonical coefficient specialization using the blueprint pullback-from-point comparison
(blueprint: lem-sfb-coefficient-sections-localization).

Stage-2 validation: N6 checked the recorded statement, dependency interfaces, and
universe parameters against the shared live library on 2026-10-18.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The unit morphism of the canonical coefficient ring.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X :=
  MonObj.one (X := condensedRingObj Λ X)

/-- The graph of a map to a test object, as a map from the final object to its base change.
Source: Stacks, Tag 03CE (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionGraph {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    Scheme.ProEt.mk (𝟙 X) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T :=
  MorphismProperty.Over.homMk
    (pullback.lift a (𝟙 X) (ha.trans (Category.id_comp f).symm))
    (pullback.lift_snd _ _ _) trivial

/-- Evaluate a sheaf morphism into a direct image and restrict along a graph.
The coefficient section maps below are specializations of this construction.
Source: Stacks, Tag 03CE (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionMapOfHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (η : R ⟶ (lowerStar Ab.{u + 1} f).obj S)
    (T : Y.ProEt) (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    R.obj.obj (op T) ⟶ S.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  η.hom.app (op T) ≫ S.obj.map (sfbSectionGraph f T a ha).op

/-- The section map `θ_T`: apply the actual coefficient mate `η` and restrict along the
 diagonal. This is the evaluation of `α` after inverse-image restriction, without choosing
 an arbitrary isomorphism. Source: Stacks, Tags 00Y0 and 03CE
(blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientSectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (T : B.ProEt) :
    (condensedRingObj Λ B).obj.obj (op T) ⟶
      (condensedRingObj Λ T.left).obj.obj (op (Scheme.ProEt.mk (𝟙 T.left))) :=
  sfbSectionMapOfHom (X := T.left) (Y := B) T.hom
    (condensedRingObj Λ B) (condensedRingObj Λ T.left)
    (condensedPushforwardHom (X := T.left) (Y := B) Λ T.hom) T
    (𝟙 T.left) (Category.id_comp T.hom)

/-- The global-section map `f^sharp`, expressed by the coefficient mate and the canonical
map from the final object to its base change. Source: Stacks, Tag 03EH
(blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientGlobalMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (condensedRingObj Λ Y).obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶
      (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (condensedPushforwardHom Λ f) (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)

private noncomputable abbrev sectionRing {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (T : X.ProEt) : CommRingCat.{u + 1} :=
  (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) R).obj (op T)

private lemma graphDiagonal_eq {B : Scheme.{u}} (V : B.ProEt) :
    sfbSectionGraph V.hom V (𝟙 V.left) (Category.id_comp V.hom) =
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial).unit.app
        (Scheme.ProEt.mk (𝟙 V.left)) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).map
        (MorphismProperty.Over.homMk (𝟙 V.left) (by simp) :
          (MorphismProperty.Over.map ⊤ V.prop).obj (Scheme.ProEt.mk (𝟙 V.left)) ⟶ V) := by
  apply MorphismProperty.Over.Hom.ext
  simp only [MorphismProperty.Comma.comp_left,
    MorphismProperty.Over.pullback_map_left,
    MorphismProperty.Over.mapPullbackAdj_unit_app]
  apply pullback.hom_ext
  · simp only [sfbSectionGraph, Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
      Scheme.ProEt.mk_hom, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      Category.assoc, limit.lift_π, PullbackCone.mk_π_app]
    change 𝟙 V.left = pullback.lift (f := 𝟙 V.left ≫ V.hom) (g := V.hom)
      (𝟙 V.left) (𝟙 V.left) _ ≫ pullback.fst (𝟙 V.left ≫ V.hom) V.hom ≫ 𝟙 V.left
    rw [pullback.lift_fst_assoc, Category.id_comp]
  · simp only [sfbSectionGraph, Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
      Scheme.ProEt.mk_hom, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      Category.assoc, limit.lift_π, PullbackCone.mk_π_app]
    change 𝟙 V.left = pullback.lift (f := 𝟙 V.left ≫ V.hom) (g := V.hom)
      (𝟙 V.left) (𝟙 V.left) _ ≫ pullback.snd (𝟙 V.left ≫ V.hom) V.hom
    exact (pullback.lift_snd _ _ _).symm

private lemma objectSectionMap_factor {B : Scheme.{u}} (V : B.ProEt)
    (F : Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
    (φ : F ⟶ (lowerStar Ab.{u + 1} V.hom).obj G) :
    φ.hom.app (op V) ≫ G.obj.map
        (sfbSectionGraph V.hom V (𝟙 V.left) (Category.id_comp V.hom)).op =
      F.obj.map
        (MorphismProperty.Over.homMk (𝟙 V.left) (by simp) :
          (MorphismProperty.Over.map ⊤ V.prop).obj (Scheme.ProEt.mk (𝟙 V.left)) ⟶ V).op ≫
      (((localizationRestrictionLowerStarAdjunction Ab.{u + 1} V.hom V.prop).homEquiv
        F G).symm φ).hom.app (op (Scheme.ProEt.mk (𝟙 V.left))) := by
  rw [Adjunction.homEquiv_counit]
  change _ = _ ≫ (φ.hom.app _ ≫ _)
  rw [← Category.assoc, φ.hom.naturality, Category.assoc]
  congr 1
  change G.obj.map _ = G.obj.map _ ≫ G.obj.map _
  rw [← Functor.map_comp]
  exact congrArg (fun a ↦ G.obj.map a.op) (graphDiagonal_eq V)

private lemma objectSectionMap_isIso {B : Scheme.{u}} (V : B.ProEt)
    (F : Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
    (φ : F ⟶ (lowerStar Ab.{u + 1} V.hom).obj G)
    [IsIso (((localizationRestrictionLowerStarAdjunction Ab.{u + 1} V.hom V.prop).homEquiv
      F G).symm φ)] :
    IsIso (sfbSectionMapOfHom V.hom F G φ V (𝟙 V.left) (Category.id_comp V.hom)) := by
  dsimp only [sfbSectionMapOfHom]
  rw [objectSectionMap_factor]
  have : IsIso (MorphismProperty.Over.homMk (𝟙 V.left) (by simp) :
      (MorphismProperty.Over.map ⊤ V.prop).obj (Scheme.ProEt.mk (𝟙 V.left)) ⟶ V) := by
    let e : (MorphismProperty.Over.map ⊤ V.prop).obj
        (Scheme.ProEt.mk (𝟙 V.left)) ≅ V :=
      MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp)
    change IsIso e.hom
    infer_instance
  infer_instance

private lemma objectSectionMap_isIso_of_pullback {B : Scheme.{u}} (V : B.ProEt)
    (F : Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
    (α : (upperStar Ab.{u + 1} V.hom).obj F ⟶ G) [IsIso α]
    (φ : F ⟶ (lowerStar Ab.{u + 1} V.hom).obj G)
    (hφ : (upperStarLowerStarAdjunction Ab.{u + 1} V.hom).homEquiv F G α = φ) :
    IsIso (sfbSectionMapOfHom V.hom F G φ V (𝟙 V.left) (Category.id_comp V.hom)) := by
  have hm : ((localizationRestrictionLowerStarAdjunction Ab.{u + 1}
      V.hom V.prop).homEquiv F G).symm φ =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} V.hom V.prop).inv.app F ≫ α := by
    apply ((localizationRestrictionLowerStarAdjunction Ab.{u + 1}
      V.hom V.prop).homEquiv F G).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
    rw [upperStarIsoLocalizationRestriction, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact hφ.symm
  have hi : IsIso (((localizationRestrictionLowerStarAdjunction Ab.{u + 1}
      V.hom V.prop).homEquiv F G).symm φ) := by
    rw [hm]
    infer_instance
  exact @objectSectionMap_isIso _ V F G φ hi

private lemma sectionMap_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {B : Scheme.{u}} (V : B.ProEt) : IsIso (sfbCoefficientSectionMap Λ V) := by
  exact objectSectionMap_isIso_of_pullback V (condensedRingObj Λ B)
    (condensedRingObj Λ V.left) (condensedPullbackHom Λ V.hom)
    (condensedPushforwardHom Λ V.hom)
    (Adjunction.homEquiv_unit _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma graph_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Z.ProEt) (a : Y ⟶ T.left) (ha : a ≫ T.hom = g) :
    sfbSectionGraph (f ≫ g) T (f ≫ a) (by rw [Category.assoc, ha]) ≫
        (MorphismProperty.Over.pullbackComp f g).hom.app T =
      sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f) ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
          (sfbSectionGraph g T a ha) := by
  apply MorphismProperty.Over.Hom.ext
  change (sfbSectionGraph (f ≫ g) T (f ≫ a)
      (by rw [Category.assoc, ha])).left ≫
      ((MorphismProperty.Over.pullbackComp f g).hom.app T).left =
    (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).left ≫
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
        (sfbSectionGraph g T a ha)).left
  simp only [MorphismProperty.Over.pullback_map_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [sfbSectionGraph, MorphismProperty.Over.pullbackComp,
        MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.isoMk, Category.assoc]
    · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Functor.comp_obj, sfbSectionGraph,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, MorphismProperty.Over.pullbackComp,
        MorphismProperty.Over.isoMk, eqToIso_refl, NatIso.ofComponents_hom_app,
        MorphismProperty.Comma.isoMk_hom_left, Iso.trans_hom, pullback.congrHom_hom,
        pullback.map_id, Iso.symm_hom, Category.id_comp, Category.assoc,
        pullbackLeftPullbackSndIso_inv_fst_snd, limit.lift_π_assoc, cospan_right,
        PullbackCone.mk_π_app, limit.lift_π, cospan_left]
      exact (Category.id_comp f).trans (Category.comp_id f).symm
  · simp [sfbSectionGraph, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.isoMk, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma objectSectionMap_restrict {B : Scheme.{u}} (V W : B.ProEt) (h : W ⟶ V)
    (F : Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
    (η : F ⟶ (lowerStar Ab.{u + 1} W.hom).obj G) :
    F.obj.map h.op ≫ sfbSectionMapOfHom W.hom F G η W (𝟙 W.left) (Category.id_comp W.hom) =
      sfbSectionMapOfHom W.hom F G η V h.left (MorphismProperty.Over.w h) := by
  dsimp only [sfbSectionMapOfHom]
  rw [← Category.assoc, η.hom.naturality, Category.assoc]
  change _ ≫ (G.obj.map _ ≫ G.obj.map _) = _
  rw [← Functor.map_comp]
  congr 1
  congr 1
  apply Quiver.Hom.unop_inj
  change sfbSectionGraph W.hom W (𝟙 W.left) (Category.id_comp W.hom) ≫
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).map h = _
  apply MorphismProperty.Over.Hom.ext
  change (sfbSectionGraph W.hom W (𝟙 W.left) (Category.id_comp W.hom)).left ≫
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).map h).left = _
  simp only [MorphismProperty.Over.pullback_map_left]
  apply pullback.hom_ext
  · simp only [Functor.id_obj, Functor.const_obj_obj, sfbSectionGraph,
      MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left, Functor.op_obj,
      Quiver.Hom.unop_op]
    exact Category.id_comp h.left
  · simp only [Functor.id_obj, Functor.const_obj_obj, sfbSectionGraph,
      MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, Functor.op_obj, Quiver.Hom.unop_op]

private lemma sectionMap_restrict
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (V W : B.ProEt) (h : W ⟶ V) :
    (condensedRingObj Λ B).obj.map h.op ≫ sfbCoefficientSectionMap Λ W =
      sfbSectionMapOfHom W.hom (condensedRingObj Λ B) (condensedRingObj Λ W.left)
        (condensedPushforwardHom Λ W.hom) V h.left (MorphismProperty.Over.w h) := by
  exact objectSectionMap_restrict V W h (condensedRingObj Λ B) (condensedRingObj Λ W.left)
    (condensedPushforwardHom Λ (X := W.left) (Y := B) W.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma objectSectionMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (H : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ηg : F ⟶ (lowerStar Ab.{u + 1} g).obj G)
    (ηf : G ⟶ (lowerStar Ab.{u + 1} f).obj H)
    (ηc : F ⟶ (lowerStar Ab.{u + 1} (f ≫ g)).obj H)
    (hc : ηg ≫ (lowerStar Ab.{u + 1} g).map ηf ≫
      (lowerStarComp Ab.{u + 1} f g).hom.app H = ηc)
    (T : Z.ProEt) (a : Y ⟶ T.left) (ha : a ≫ T.hom = g) :
    sfbSectionMapOfHom g F G ηg T a ha ≫
        sfbSectionMapOfHom f G H ηf (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f) =
      sfbSectionMapOfHom (f ≫ g) F H ηc T (f ≫ a)
        (by rw [Category.assoc, ha]) := by
  dsimp only [sfbSectionMapOfHom]
  rw [← hc]
  simp only [Category.assoc]
  rw [← Category.assoc (G.obj.map (sfbSectionGraph g T a ha).op), ηf.hom.naturality]
  change _ ≫ (_ ≫ (H.obj.map _ ≫ H.obj.map _)) =
    _ ≫ (_ ≫ (H.obj.map _ ≫ H.obj.map _))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  exact (graph_comp f g T a ha).symm

private noncomputable def coefficientGraphMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    (condensedRingObj Λ Y).obj.obj (op T) ⟶
      (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (condensedPushforwardHom Λ f) T a ha

private lemma coefficientGraphMap_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f f' : X ⟶ Y) (hf : f = f') (T : Y.ProEt)
    (a a' : X ⟶ T.left) (ha : a ≫ T.hom = f) (ha' : a' ≫ T.hom = f')
    (he : a = a') : coefficientGraphMap Λ f T a ha =
      coefficientGraphMap Λ f' T a' ha' := by
  subst f'
  subst a'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma sectionMap_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (V W : B.ProEt) (h : W ⟶ V) :
    sfbCoefficientSectionMap Λ V ≫ sfbCoefficientGlobalMap Λ h.left =
      (condensedRingObj Λ B).obj.map h.op ≫ sfbCoefficientSectionMap Λ W := by
  rw [sectionMap_restrict]
  have hm := objectSectionMap_comp h.left V.hom (condensedRingObj Λ B)
    (condensedRingObj Λ V.left) (condensedRingObj Λ W.left)
    (condensedPushforwardHom Λ (X := V.left) (Y := B) V.hom)
    (condensedPushforwardHom Λ (X := W.left) (Y := V.left) h.left)
    (condensedPushforwardHom Λ (h.left ≫ V.hom))
    (condensedPushforwardHom_comp Λ h.left V.hom).symm
    V (𝟙 V.left) (Category.id_comp V.hom)
  calc
    _ = coefficientGraphMap Λ (h.left ≫ V.hom) V (h.left ≫ 𝟙 V.left)
        (by rw [Category.assoc, Category.id_comp]) := hm
    _ = coefficientGraphMap Λ W.hom V h.left (MorphismProperty.Over.w h) :=
      coefficientGraphMap_congr Λ (h.left ≫ V.hom) W.hom
        (MorphismProperty.Over.w h) V (h.left ≫ 𝟙 V.left) h.left
        (by rw [Category.assoc, Category.id_comp]) (MorphismProperty.Over.w h)
        (Category.comp_id h.left)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def regularExtensionIso
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S := by
  let e := Mod.regularIsoComapRegular φ
  let q := Mod.extendHom φ e.hom
  haveI : (Mod.comap φ).IsEquivalence := (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  haveI : (Mod.extendScalars φ).IsEquivalence :=
    (Mod.extendRestrictAdjunction φ).isEquivalence_left_of_isEquivalence_right
  have hu : IsIso (Mod.extendUnit φ (Mod.regular R)) := by
    have he : (Mod.extendRestrictAdjunction φ).unit.app (Mod.regular R) =
        Mod.extendUnit φ (Mod.regular R) := by
      simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_unit_app]
      change Mod.extendUnit φ (Mod.regular R) ≫ (Mod.comap φ).map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← he]
    infer_instance
  have hq : Mod.extendUnit φ (Mod.regular R) ≫ (Mod.comap φ).map q = e.hom :=
    (Mod.extendHomEquiv φ (Mod.regular R) (Mod.regular S)).apply_symm_apply e.hom
  have : IsIso ((Mod.comap φ).map q) := by
    have : IsIso (Mod.extendUnit φ (Mod.regular R) ≫ (Mod.comap φ).map q) := by
      rw [hq]
      infer_instance
    exact IsIso.of_isIso_comp_left (Mod.extendUnit φ (Mod.regular R)) _
  have : IsIso q := isIso_of_reflects_iso q (Mod.comap φ)
  exact asIso q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section RegularPullback

variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory D]
  [MonoidalClosed D] [HasEqualizers D] [HasCoequalizers D]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R]
  [IsCommMonObj (F.obj R)] (S : D) [MonObj S]
  (φ : F.obj R ⟶ S) [IsMonHom φ] [IsIso φ]

private noncomputable def regularPullbackIso :
    ((F.mapMod R) ⋙ Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S :=
  regularExtensionIso φ

end RegularPullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.ProEtale
