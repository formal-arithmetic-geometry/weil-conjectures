/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence

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

/-- The evaluated unit of an internal monoid of abelian sheaves.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSheafSectionOne {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (unit : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ R) (T : X.ProEt) :
    R.obj.obj (op T) :=
  ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      unit).app (op T)).hom (ULift.up (1 : ℤ))

/-- The evaluated product of an internal monoid of abelian sheaves.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSheafSectionMul {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (mul : R ⊗ R ⟶ R) (T : X.ProEt)
    (a b : R.obj.obj (op T)) : R.obj.obj (op T) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R R ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      mul).app (op T)).hom (a ⊗ₜ[ℤ] b)

/-- The unit morphism of the canonical coefficient ring.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X :=
  MonObj.one (X := condensedRingObj Λ X)

/-- The multiplication morphism of the canonical coefficient ring.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientMul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    condensedRingObj Λ X ⊗ condensedRingObj Λ X ⟶ condensedRingObj Λ X :=
  MonObj.mul (X := condensedRingObj Λ X)

/-- The unit of the section ring, obtained by evaluating the internal ring unit.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionOne
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt) : (condensedRingObj Λ X).obj.obj (op T) :=
  sfbSheafSectionOne (condensedRingObj Λ X)
    (sfbCoefficientUnit Λ X) T

/-- Multiplication of sections, using the lax tensorator of evaluation followed by
internal multiplication. Source: Stacks, Tag 00Y0
(blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionMul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt)
    (a b : (condensedRingObj Λ X).obj.obj (op T)) :
    (condensedRingObj Λ X).obj.obj (op T) :=
  sfbSheafSectionMul (condensedRingObj Λ X)
    (sfbCoefficientMul Λ X) T a b

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

/-- The unique arrow to the final pro-etale test object.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
def sfbSectionFinalArrow (X : Scheme.{u}) (T : X.ProEt) :
    T ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk T.hom (Category.comp_id T.hom) trivial

private noncomputable abbrev sectionRing {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (T : X.ProEt) : CommRingCat.{u + 1} :=
  (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) R).obj (op T)

private noncomputable def sectionHom {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] (T : X.ProEt) :
    sectionRing R T →+* sectionRing S T := by
  let g := (Monoidal.MonFunctorCategoryEquivalence.functor
    (C := X.ProEtᵒᵖ) (D := Ab.{u + 1})).map
      ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMon.map
        (Mon.Hom.mk (M := Mon.mk R) (N := Mon.mk S) f))
  exact InternalAbelianSheafModule.ringHom (g.app (op T)).hom

private noncomputable def continuousSectionHom
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J Ab.{u + 1}] [HasSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    [F.IsContinuous J K]
    (R : Sheaf K Ab.{u + 1}) [MonObj R] [IsCommMonObj R] (T : Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings J
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj R)).obj T →+*
      (InternalAbelianSheafModule.sectionRings K R).obj (F.op.obj T) := by
  letI := Sheaf.monoidalCategory (J := J) (A := Ab.{u + 1})
  letI := Sheaf.monoidalCategory (J := K) (A := Ab.{u + 1})
  refine { AddMonoidHom.id _ with map_one' := ?_, map_mul' := ?_ }
  · change ((Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1})).app T ≫
      (Functor.LaxMonoidal.ε (F.sheafPushforwardContinuous Ab.{u + 1} J K)).hom.app T ≫
        (MonObj.one (X := R)).hom.app (F.op.obj T)).hom (ULift.up 1) =
      ((Functor.LaxMonoidal.ε (sheafToPresheaf K Ab.{u + 1})).app (F.op.obj T) ≫
        (MonObj.one (X := R)).hom.app (F.op.obj T)).hom (ULift.up 1)
    rw [← Category.assoc]
    rw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
    rfl
  · intro a b
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj R)
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj R)).app T ≫
      (Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous Ab.{u + 1} J K) R R).hom.app T ≫
        (MonObj.mul (X := R)).hom.app (F.op.obj T)).hom (a ⊗ₜ[ℤ] b) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf K Ab.{u + 1}) R R).app (F.op.obj T) ≫
        (MonObj.mul (X := R)).hom.app (F.op.obj T)).hom (a ⊗ₜ[ℤ] b)
    rw [← Category.assoc]
    rw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app]
    rfl

private noncomputable def pushforwardSectionHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (T : Y.ProEt) :
    sectionRing ((lowerStar Ab.{u + 1} f).obj R) T →+*
      sectionRing R ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T) :=
  continuousSectionHom (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) R (op T)

private noncomputable def sectionModuleMultiplication
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (r : R.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    Mod.regular R ⟶ Mod.regular R := by
  let F := InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology X) R
  let M := (F.obj (Mod.regular R)).val
  apply (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (Scheme.ProEt.topology X) R).preimage
  refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
  · let A := sectionRing R U.unop
    letI : Module A (M.obj U) := (M.obj U).isModule
    let t : A := R.obj.map (sfbSectionFinalArrow X U.unop).op r
    exact ConcreteCategory.ofHom (C := ModuleCat A) (X := M.obj U) (Y := M.obj U)
      (LinearMap.lsmul A (M.obj U) t)
  · intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (R.obj.map (sfbSectionFinalArrow X V.unop).op r : sectionRing R V.unop) •
        M.map f a = M.map f
          ((R.obj.map (sfbSectionFinalArrow X U.unop).op r : sectionRing R U.unop) • a)
    rw [M.map_smul]
    congr 1
    change R.obj.map (sfbSectionFinalArrow X V.unop).op r =
      (R.obj.map (sfbSectionFinalArrow X U.unop).op ≫ R.obj.map f) r
    rw [← Functor.map_comp]
    congr 3
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    exact (MorphismProperty.Over.w f.unop).symm

private noncomputable def multiplicationSheafMap
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (r : R.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) : R ⟶ R :=
  (sectionModuleMultiplication R r).hom

@[irreducible] private noncomputable def multiplySection
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (r : R.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    Mod.regular R ⟶ Mod.regular R :=
  { hom := multiplicationSheafMap R r
    isModHom := (sectionModuleMultiplication R r).isModHom }

private lemma multiplySection_apply
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (r : R.obj.obj (op (Scheme.ProEt.mk (𝟙 X))))
    (T : X.ProEt) (a : R.obj.obj (op T)) :
    (multiplySection R r).hom.hom.app (op T) a =
      sfbSheafSectionMul R (MonObj.mul (X := R)) T
        (R.obj.map (sfbSectionFinalArrow X T).op r) a := by
  unfold multiplySection multiplicationSheafMap sectionModuleMultiplication
  rfl

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma sectionMap_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {B : Scheme.{u}} (V : B.ProEt) : IsIso (sfbCoefficientSectionMap Λ V) := by
  exact objectSectionMap_isIso_of_pullback V (condensedRingObj Λ B)
    (condensedRingObj Λ V.left) (condensedPullbackHom Λ V.hom)
    (condensedPushforwardHom Λ V.hom)
    (Adjunction.homEquiv_unit _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma graph_global_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt) :
    sfbSectionFinalArrow X ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T) ≫
        sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f) =
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map (sfbSectionFinalArrow Y T) := by
  apply MorphismProperty.Over.Hom.ext
  change (sfbSectionFinalArrow X _).left ≫
      (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).left = _
  simp only [MorphismProperty.Over.pullback_map_left]
  apply pullback.hom_ext
  · simp [sfbSectionGraph, sfbSectionFinalArrow, Category.assoc, pullback.condition]
  · simp only [Functor.id_obj, Functor.const_obj_obj, sfbSectionFinalArrow,
      MorphismProperty.Over.pullback_obj_hom, MorphismProperty.Over.homMk_hom,
      Over.homMk_left, sfbSectionGraph, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.condition]
    exact Category.comp_id _

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
private lemma objectGlobalMap_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (η : F ⟶ (lowerStar Ab.{u + 1} f).obj G) (T : Y.ProEt) :
    (η.hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫ G.obj.map
        (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).op) ≫
      G.obj.map (sfbSectionFinalArrow X
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T)).op =
      F.obj.map (sfbSectionFinalArrow Y T).op ≫ η.hom.app (op T) := by
  rw [η.hom.naturality, Category.assoc]
  change _ ≫ (G.obj.map _ ≫ G.obj.map _) = _
  rw [← Functor.map_comp]
  congr 1
  exact congrArg (fun a ↦ G.obj.map a.op) (graph_global_restrict f T)

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
private lemma multiplySection_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (η : R ⟶ (lowerStar Ab.{u + 1} f).obj S) [IsMonHom η]
    (r : R.obj.obj (op (Scheme.ProEt.mk (𝟙 Y)))) :
    (multiplySection R r).hom ≫ η = η ≫ (lowerStar Ab.{u + 1} f).map
      (multiplySection S ((η.hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫ S.obj.map
        (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).op) r)).hom := by
  apply Sheaf.hom_ext
  ext U a
  change η.hom.app U ((multiplySection R r).hom.hom.app U a) =
    (multiplySection S _).hom.hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U) (η.hom.app U a)
  erw [multiplySection_apply R r U.unop a,
    multiplySection_apply S _
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop) (η.hom.app U a)]
  let σ := (pushforwardSectionHom f S U.unop).comp (sectionHom η U.unop)
  have hr := ConcreteCategory.congr_hom (objectGlobalMap_restrict f R S η U.unop) r
  change S.obj.map (sfbSectionFinalArrow X
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop)).op
        ((η.hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫ S.obj.map
          (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).op) r) =
    σ (R.obj.map (sfbSectionFinalArrow Y U.unop).op r) at hr
  exact (σ.map_mul (R.obj.map (sfbSectionFinalArrow Y U.unop).op r) a).trans
    (congrArg (fun z : sectionRing S
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop) ↦ z * σ a) hr.symm)

private lemma multiplySection_pullback_of_mate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (α : (upperStar Ab.{u + 1} f).obj R ⟶ S)
    (η : R ⟶ (lowerStar Ab.{u + 1} f).obj S) [IsMonHom η]
    (hη : (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv R S α = η)
    (r : R.obj.obj (op (Scheme.ProEt.mk (𝟙 Y)))) :
    (upperStar Ab.{u + 1} f).map (multiplySection R r).hom ≫ α =
      α ≫ (multiplySection S
        ((sfbSectionMapOfHom f R S η (Scheme.ProEt.mk (𝟙 Y)) f
          (Category.comp_id f)).hom r)).hom := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change (multiplySection R r).hom ≫
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv R S α =
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv R S α ≫ _
  rw [hη]
  exact multiplySection_pushforward f R S η r

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

private lemma regularExtensionIso_unit
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    Mod.extendUnitHom φ (Mod.regular R) ≫ (regularExtensionIso φ).hom.hom = φ := by
  exact Mod.extendUnitHom_extendHom φ (Mod.regularIsoComapRegular φ).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma regularExtensionIso_naturality
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (a : Mod.regular R ⟶ Mod.regular R) (b : Mod.regular S ⟶ Mod.regular S)
    (h : a.hom ≫ φ = φ ≫ b.hom) :
    (Mod.extendScalars φ).map a ≫ (regularExtensionIso φ).hom =
      (regularExtensionIso φ).hom ≫ b := by
  apply ((Mod.extendRestrictAdjunction φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change a ≫ (Mod.extendHomEquiv φ (Mod.regular R) (Mod.regular S))
      (Mod.extendHom φ (Mod.regularIsoComapRegular φ).hom) =
    (Mod.extendHomEquiv φ (Mod.regular R) (Mod.regular S))
      (Mod.extendHom φ (Mod.regularIsoComapRegular φ).hom) ≫ (Mod.comap φ).map b
  have he := (Mod.extendHomEquiv φ (Mod.regular R) (Mod.regular S)).apply_symm_apply
    (Mod.regularIsoComapRegular φ).hom
  change (Mod.extendHomEquiv φ (Mod.regular R) (Mod.regular S))
    (Mod.extendHom φ (Mod.regularIsoComapRegular φ).hom) = _ at he
  rw [he]
  apply Mod.hom_ext
  exact h

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

private lemma regularPullbackIso_unit :
    Mod.extendUnitHom φ ((F.mapMod R).obj (Mod.regular R)) ≫
      (regularPullbackIso F R S φ).hom.hom = φ :=
  regularExtensionIso_unit φ

private lemma regularPullbackIso_naturality
    (a : Mod.regular R ⟶ Mod.regular R) (b : Mod.regular S ⟶ Mod.regular S)
    (h : F.map a.hom ≫ φ = φ ≫ b.hom) :
    ((F.mapMod R) ⋙ Mod.extendScalars φ).map a ≫ (regularPullbackIso F R S φ).hom =
      (regularPullbackIso F R S φ).hom ≫ b :=
  regularExtensionIso_naturality φ ((F.mapMod R).map a) b h

private lemma regularPullbackIso_naturality_hom
    (a : Mod.regular R ⟶ Mod.regular R) (b : Mod.regular S ⟶ Mod.regular S)
    (h : F.map a.hom ≫ φ = φ ≫ b.hom) :
    (((F.mapMod R) ⋙ Mod.extendScalars φ).map a).hom ≫
        (regularPullbackIso F R S φ).hom.hom =
      (regularPullbackIso F R S φ).hom.hom ≫ b.hom :=
  congrArg Mod.Hom.hom (regularPullbackIso_naturality F R S φ a b h)

end RegularPullback

private lemma section_square_apply {A B C D : Ab.{u + 1}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (he : f ≫ g = h ≫ k) (a : A) : g.hom (f.hom a) = k.hom (h a) :=
  congrArg (fun φ : A ⟶ D ↦ φ.hom a) he

private lemma sectionUnit_map {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (uR : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ R)
    (uS : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ S)
    (η : R ⟶ S) (h : uR ≫ η = uS) (T : X.ProEt) :
    (η.hom.app (op T)).hom (sfbSheafSectionOne R uR T) =
      sfbSheafSectionOne S uS T := by
  have ht := congrArg (fun g ↦ g.hom.app (op T)) h
  change ((Functor.LaxMonoidal.ε
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})).app (op T) ≫
      uR.hom.app (op T) ≫ η.hom.app (op T)).hom (ULift.up (1 : ℤ)) = _
  rw [show uR.hom.app (op T) ≫ η.hom.app (op T) = uS.hom.app (op T) from ht]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma objectSection_one_of_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (uR : 𝟙_ (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) ⟶ R)
    (uS : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ S)
    (η : R ⟶ (lowerStar Ab.{u + 1} f).obj S)
    (h : uR ≫ η = Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) ≫
      (lowerStar Ab.{u + 1} f).map uS)
    (T : Y.ProEt) (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    (sfbSectionMapOfHom f R S η T a ha).hom (sfbSheafSectionOne R uR T) =
      sfbSheafSectionOne S uS (Scheme.ProEt.mk (𝟙 X)) := by
  have h₁ := sectionUnit_map uR
    (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) ≫
      (lowerStar Ab.{u + 1} f).map uS) η h T
  have h₂ : sfbSheafSectionOne ((lowerStar Ab.{u + 1} f).obj S)
      (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) ≫
        (lowerStar Ab.{u + 1} f).map uS) T =
      sfbSheafSectionOne S uS
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T) := by
    change ((Functor.LaxMonoidal.ε
      (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})).app (op T) ≫
      (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f)).hom.app (op T) ≫
        uS.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))).hom
          (ULift.up (1 : ℤ)) = _
    rw [← Category.assoc]
    erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
    rfl
  let v := Functor.LaxMonoidal.ε
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map uS
  have h₃ : (S.obj.map (sfbSectionGraph f T a ha).op).hom
      (sfbSheafSectionOne S uS
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T)) =
      sfbSheafSectionOne S uS (Scheme.ProEt.mk (𝟙 X)) := by
    have hv := v.naturality (sfbSectionGraph f T a ha).op
    have he : v.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T)) ≫
        S.obj.map (sfbSectionGraph f T a ha).op =
          v.app (op (Scheme.ProEt.mk (𝟙 X))) := by
      simpa using hv.symm
    exact congrArg (fun z ↦ z.hom (ULift.up (1 : ℤ))) he
  exact (congrArg (fun z ↦ (S.obj.map (sfbSectionGraph f T a ha).op).hom z) h₁).trans
    ((congrArg (fun z ↦ (S.obj.map (sfbSectionGraph f T a ha).op).hom z) h₂).trans h₃)

private lemma coefficient_one_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfbCoefficientUnit Λ Y ≫ condensedPushforwardHom Λ f =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) ≫
        (lowerStar Ab.{u + 1} f).map (sfbCoefficientUnit Λ X) :=
  IsMonHom.one_hom (condensedPushforwardHom Λ f)

private lemma coefficient_one_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt) :
    sfbSectionOne Λ X T =
      sfbSheafSectionOne (condensedRingObj Λ X) (sfbCoefficientUnit Λ X) T := rfl

private lemma coefficientObjectSection_one_raw
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    (sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
      (condensedPushforwardHom Λ f) T a ha).hom
        (sfbSheafSectionOne (condensedRingObj Λ Y) (sfbCoefficientUnit Λ Y) T) =
        sfbSheafSectionOne (condensedRingObj Λ X) (sfbCoefficientUnit Λ X)
          (Scheme.ProEt.mk (𝟙 X)) := by
  have h := @objectSection_one_of_one X Y f
    (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (sfbCoefficientUnit Λ Y) (sfbCoefficientUnit Λ X)
    (condensedPushforwardHom (X := X) (Y := Y) Λ f)
    (coefficient_one_hom (X := X) (Y := Y) Λ f) T a ha
  exact h

private lemma coefficientObjectSection_one
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    (sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
      (condensedPushforwardHom Λ f) T a ha).hom (sfbSectionOne Λ Y T) =
        sfbSectionOne Λ X (Scheme.ProEt.mk (𝟙 X)) := by
  rw [coefficient_one_formula, coefficient_one_formula]
  exact coefficientObjectSection_one_raw Λ f T a ha

private lemma sectionMul_map {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (mR : R ⊗ R ⟶ R) (mS : S ⊗ S ⟶ S)
    (η : R ⟶ S) (h : mR ≫ η = (η ⊗ₘ η) ≫ mS) (T : X.ProEt)
    (a b : R.obj.obj (op T)) :
    (η.hom.app (op T)).hom (sfbSheafSectionMul R mR T a b) =
      sfbSheafSectionMul S mS T ((η.hom.app (op T)).hom a)
        ((η.hom.app (op T)).hom b) := by
  let P := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  have hP : Functor.LaxMonoidal.μ P R R ≫ P.map mR ≫ P.map η =
      (P.map η ⊗ₘ P.map η) ≫ Functor.LaxMonoidal.μ P S S ≫ P.map mS := by
    rw [← P.map_comp, h, P.map_comp, ← Category.assoc,
      ← Functor.LaxMonoidal.μ_natural, Category.assoc]
  exact congrArg (fun z ↦ (z.app (op T)).hom (a ⊗ₜ[ℤ] b)) hP

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma objectSection_mul_of_mul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (mR : R ⊗ R ⟶ R) (mS : S ⊗ S ⟶ S)
    (η : R ⟶ (lowerStar Ab.{u + 1} f).obj S)
    (h : mR ≫ η = (η ⊗ₘ η) ≫ Functor.LaxMonoidal.μ (lowerStar Ab.{u + 1} f) S S ≫
      (lowerStar Ab.{u + 1} f).map mS)
    (T : Y.ProEt) (a : X ⟶ T.left) (ha : a ≫ T.hom = f)
    (r t : R.obj.obj (op T)) :
    (sfbSectionMapOfHom f R S η T a ha).hom (sfbSheafSectionMul R mR T r t) =
      sfbSheafSectionMul S mS (Scheme.ProEt.mk (𝟙 X))
        ((sfbSectionMapOfHom f R S η T a ha).hom r)
        ((sfbSectionMapOfHom f R S η T a ha).hom t) := by
  let L := lowerStar Ab.{u + 1} f
  let U := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T
  let r' := (η.hom.app (op T)).hom r
  let t' := (η.hom.app (op T)).hom t
  have h₁ := sectionMul_map mR (Functor.LaxMonoidal.μ L S S ≫ L.map mS) η h T r t
  have h₂ : sfbSheafSectionMul (L.obj S)
      (Functor.LaxMonoidal.μ L S S ≫ L.map mS) T r' t' =
      sfbSheafSectionMul S mS U r' t' := by
    change ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (L.obj S) (L.obj S)).app
      (op T) ≫ (Functor.LaxMonoidal.μ L S S).hom.app (op T) ≫
        mS.hom.app (op U)).hom (r' ⊗ₜ[ℤ] t') = _
    rw [← Category.assoc]
    erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) S S (op T)]
    rfl
  let P := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let v := Functor.LaxMonoidal.μ P S S ≫ P.map mS
  let g := (sfbSectionGraph f T a ha).op
  have h₃ : (S.obj.map g).hom (sfbSheafSectionMul S mS U r' t') =
      sfbSheafSectionMul S mS (Scheme.ProEt.mk (𝟙 X))
        ((S.obj.map g).hom r') ((S.obj.map g).hom t') := by
    have hv := v.naturality g
    exact congrArg (fun z ↦ z.hom (r' ⊗ₜ[ℤ] t')) hv.symm
  exact (congrArg (fun z ↦ (S.obj.map g).hom z) h₁).trans
    ((congrArg (fun z ↦ (S.obj.map g).hom z) h₂).trans h₃)

private lemma coefficient_mul_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfbCoefficientMul Λ Y ≫ condensedPushforwardHom Λ f =
      (condensedPushforwardHom Λ f ⊗ₘ condensedPushforwardHom Λ f) ≫
        Functor.LaxMonoidal.μ (lowerStar Ab.{u + 1} f)
          (condensedRingObj Λ X) (condensedRingObj Λ X) ≫
            (lowerStar Ab.{u + 1} f).map (sfbCoefficientMul Λ X) :=
  IsMonHom.mul_hom (condensedPushforwardHom Λ f)

private lemma coefficient_mul_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt) (a b : (condensedRingObj Λ X).obj.obj (op T)) :
    sfbSectionMul Λ X T a b =
      sfbSheafSectionMul (condensedRingObj Λ X) (sfbCoefficientMul Λ X) T a b := rfl

private lemma coefficientObjectSection_mul_raw
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f)
    (r t : (condensedRingObj Λ Y).obj.obj (op T)) :
    (sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
      (condensedPushforwardHom Λ f) T a ha).hom
        (sfbSheafSectionMul (condensedRingObj Λ Y) (sfbCoefficientMul Λ Y) T r t) =
        sfbSheafSectionMul (condensedRingObj Λ X) (sfbCoefficientMul Λ X)
          (Scheme.ProEt.mk (𝟙 X))
          ((sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
            (condensedPushforwardHom Λ f) T a ha).hom r)
          ((sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
            (condensedPushforwardHom Λ f) T a ha).hom t) := by
  exact objectSection_mul_of_mul f (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (sfbCoefficientMul Λ Y) (sfbCoefficientMul Λ X)
    (condensedPushforwardHom Λ f) (coefficient_mul_hom Λ f) T a ha r t

private lemma coefficientObjectSection_mul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f)
    (r t : (condensedRingObj Λ Y).obj.obj (op T)) :
    (sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
      (condensedPushforwardHom Λ f) T a ha).hom (sfbSectionMul Λ Y T r t) =
        sfbSectionMul Λ X (Scheme.ProEt.mk (𝟙 X))
          ((sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
            (condensedPushforwardHom Λ f) T a ha).hom r)
          ((sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
            (condensedPushforwardHom Λ f) T a ha).hom t) := by
  rw [coefficient_mul_formula, coefficient_mul_formula]
  exact coefficientObjectSection_mul_raw Λ f T a ha r t

private lemma coefficient_section_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (T : B.ProEt) :
    sfbCoefficientSectionMap Λ T =
      sfbSectionMapOfHom (X := T.left) (Y := B) T.hom
        (condensedRingObj Λ B) (condensedRingObj Λ T.left)
        (condensedPushforwardHom (X := T.left) (Y := B) Λ T.hom)
        T (𝟙 T.left) (Category.id_comp T.hom) := rfl

private lemma coefficient_global_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfbCoefficientGlobalMap Λ f =
      sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
        (condensedPushforwardHom Λ f) (Scheme.ProEt.mk (𝟙 Y)) f
        (Category.comp_id f) := rfl

private lemma coefficient_mul_morphism_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    sfbCoefficientMul Λ X = MonObj.mul (X := condensedRingObj Λ X) := rfl

/-- Coefficient sections over site objects are global sections after pullback, naturally
in every morphism of test objects and compatibly with multiplication endomorphisms.
The bijective additive map with its unit and product equations is the ring isomorphism
`θ`. Global sections are evaluated at the final object. The endomorphisms `m` below
are fixed on every test object by multiplication by the restricted global section.
The regular-module isomorphism `q` is normalized by `q(1 ⊗ a) = α(a)`; linearity
then gives `q(b ⊗ a) = b α(a)`, so this is the canonical scalar-extension comparison.

Source: Stacks, sites.tex, Tags 00Y0, 03CE and 03EH; proetale.tex, Tag 098T;
blueprint `lem-sfb-eta-comp` and `def-sfb-modobj-extension`
(blueprint: lem-sfb-coefficient-sections-localization).

Proof:
1. Use weakly-etale localization for the slice equivalence and coverings. The existing
   composition/base-change adjunction makes localization restriction a left adjoint to
   direct image; uniqueness of left adjoints gives its comparison with upperStar.
2. Factor the coefficient section map as restriction along the identity-object
   isomorphism followed by the restriction-adjunction mate of the coefficient map.
   The adjoint comparison identifies that mate with an isomorphism, proving invertibility.
3. Evaluate the unit and multiplication laws of the coefficient mate. Compatibility of
   continuous direct image with the lax tensorators, followed by graph restriction,
   gives exactly the unit and product equations for the stated operations.
4. Naturality of the coefficient mate identifies ordinary restriction followed by theta
   with evaluation along the graph. The two pullback projections compute composition
   of graphs. The coefficient-mate composition law then gives theta naturality for
   arbitrary morphisms of test objects, without a monomorphism hypothesis.
5. Construct multiplication by a global section on the sectionwise regular module,
   using its restriction on each test object. The internal-to-sectionwise module
   functor is fully faithful, so this gives the required internal endomorphism.
6. Product preservation and naturality show that these multiplication maps commute
   with the coefficient mate. Transfer the identity across the upperStar/lowerStar
   adjunction to obtain its inverse-image version.
7. Transpose the regular-module comparison across extension/restriction of scalars.
   Since the coefficient map is an isomorphism, restriction is an equivalence, hence
   the transposed comparison is invertible. Its adjunction identity gives the stated
   normalization. The same Hom equivalence transfers the multiplication identity;
   theta naturality identifies the resulting scalar with the restricted section. -/
theorem sfbCoefficientSectionsLocalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) :
    (∀ V : B.ProEt, ∃ e : Over V ≌ V.left.ProEt,
      (∀ T : Over V, (e.functor.obj T).left = T.left.left) ∧
      (∀ T : Over V, HEq (e.functor.obj T).hom T.hom.left) ∧
      (∀ (T T' : Over V) (a : T ⟶ T'), HEq (e.functor.map a).left a.left.left) ∧
      (∀ T : V.left.ProEt, (e.inverse.obj T).left.left = T.left) ∧
      (∀ T : V.left.ProEt, HEq (e.inverse.obj T).hom.left T.hom) ∧
      (∀ (T T' : V.left.ProEt) (a : T ⟶ T'), HEq (e.inverse.map a).left.left a.left) ∧
      (∀ (T : V.left.ProEt) (S : Sieve T),
        S ∈ Scheme.ProEt.topology V.left T ↔
          S.functorPushforward e.inverse ∈
            (Scheme.ProEt.topology B).over V (e.inverse.obj T)) ∧
      Nonempty (upperStar Ab.{u + 1} V.hom ≅
        localizationRestriction Ab.{u + 1} V.hom V.prop)) ∧
    (∀ V : B.ProEt,
      IsIso (sfbCoefficientSectionMap Λ V) ∧
      (sfbCoefficientSectionMap Λ V).hom (sfbSectionOne Λ B V) =
        sfbSectionOne Λ V.left (Scheme.ProEt.mk (𝟙 V.left)) ∧
      ∀ a b : (condensedRingObj Λ B).obj.obj (op V),
        (sfbCoefficientSectionMap Λ V).hom (sfbSectionMul Λ B V a b) =
          sfbSectionMul Λ V.left (Scheme.ProEt.mk (𝟙 V.left))
            ((sfbCoefficientSectionMap Λ V).hom a) ((sfbCoefficientSectionMap Λ V).hom b)) ∧
    (∀ (V W : B.ProEt) (h : W ⟶ V)
      (s : (condensedRingObj Λ B).obj.obj (op V)),
      (sfbCoefficientGlobalMap Λ h.left).hom ((sfbCoefficientSectionMap Λ V).hom s) =
        (sfbCoefficientSectionMap Λ W).hom ((condensedRingObj Λ B).obj.map h.op s)) ∧
    ∃ m : ∀ (X : Scheme.{u}),
        (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) →
          (Mod.regular (condensedRingObj Λ X) ⟶ Mod.regular (condensedRingObj Λ X)),
      (∀ (X : Scheme.{u})
        (r : (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))))
        (T : X.ProEt) (a : (condensedRingObj Λ X).obj.obj (op T)),
        (m X r).hom.hom.app (op T) a = sfbSectionMul Λ X T
          ((condensedRingObj Λ X).obj.map (sfbSectionFinalArrow X T).op r) a) ∧
      ∀ (V W : B.ProEt) (h : W ⟶ V),
        ∃ q : (CondensedRing.upperStar Λ h.left).obj
            (Mod.regular (condensedRingObj Λ V.left)) ≅
              Mod.regular (condensedRingObj Λ W.left),
          Mod.extendUnitHom (condensedPullbackHom Λ h.left)
              (((upperStar Ab.{u + 1} h.left).mapMod (condensedRingObj Λ V.left)).obj
                (Mod.regular (condensedRingObj Λ V.left))) ≫ q.hom.hom =
            condensedPullbackHom Λ h.left ∧
          ∀ s : (condensedRingObj Λ B).obj.obj (op V),
            (CondensedRing.upperStar Λ h.left).map
                (m V.left ((sfbCoefficientSectionMap Λ V).hom s)) ≫ q.hom =
              q.hom ≫ m W.left ((sfbCoefficientSectionMap Λ W).hom
                ((condensedRingObj Λ B).obj.map h.op s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V
    obtain ⟨e, h₁, h₂, h₃, h₄, h₅, h₆, h₇, _⟩ :=
      (Scheme.ProEt.weaklyEtale_localization.{u, u + 1, u + 1} B V
        (CommRingCat.of (ULift.{u + 1} ℤ))).2.2.1
    exact ⟨e, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      ⟨upperStarIsoLocalizationRestriction Ab.{u + 1} V.hom V.prop⟩⟩
  · intro V
    refine ⟨sectionMap_isIso Λ V, ?_, ?_⟩
    · rw [coefficient_section_formula]
      exact coefficientObjectSection_one (X := V.left) (Y := B) Λ V.hom V
        (𝟙 V.left) (Category.id_comp V.hom)
    · intro a b
      rw [coefficient_section_formula]
      exact coefficientObjectSection_mul (X := V.left) (Y := B) Λ V.hom V
        (𝟙 V.left) (Category.id_comp V.hom) a b
  · intro V W h s
    exact section_square_apply (sfbCoefficientSectionMap Λ V)
      (sfbCoefficientGlobalMap Λ h.left) ((condensedRingObj Λ B).obj.map h.op)
      (sfbCoefficientSectionMap Λ W) (sectionMap_naturality Λ V W h) s
  · refine ⟨fun X r ↦ multiplySection (condensedRingObj Λ X) r, ?_, ?_⟩
    · intro X r T a
      rw [coefficient_mul_formula]
      rw [coefficient_mul_morphism_formula]
      exact multiplySection_apply (condensedRingObj Λ X) r T a
    · intro V W h
      let q := regularPullbackIso (upperStar Ab.{u + 1} h.left)
        (condensedRingObj Λ V.left) (condensedRingObj Λ W.left)
        (condensedPullbackHom Λ h.left)
      refine ⟨q, regularPullbackIso_unit (upperStar Ab.{u + 1} h.left)
        (condensedRingObj Λ V.left) (condensedRingObj Λ W.left)
        (condensedPullbackHom Λ h.left), ?_⟩
      intro s
      apply Mod.hom_ext
      have hp := multiplySection_pullback_of_mate (X := W.left) (Y := V.left) h.left
        (condensedRingObj Λ V.left) (condensedRingObj Λ W.left)
        (condensedPullbackHom Λ h.left) (condensedPushforwardHom Λ h.left)
        (Adjunction.homEquiv_unit _ _ _ _) ((sfbCoefficientSectionMap Λ V).hom s)
      have hn := section_square_apply (sfbCoefficientSectionMap Λ V)
        (sfbCoefficientGlobalMap Λ h.left) ((condensedRingObj Λ B).obj.map h.op)
        (sfbCoefficientSectionMap Λ W) (sectionMap_naturality Λ V W h) s
      let t := (sfbSectionMapOfHom (X := W.left) (Y := V.left) h.left (condensedRingObj Λ V.left)
        (condensedRingObj Λ W.left)
        (condensedPushforwardHom (X := W.left) (Y := V.left) Λ h.left)
        (Scheme.ProEt.mk (𝟙 V.left)) h.left (Category.comp_id h.left)).hom
          ((sfbCoefficientSectionMap Λ V).hom s)
      rw [coefficient_global_formula (X := W.left) (Y := V.left)] at hn
      change t = (sfbCoefficientSectionMap Λ W).hom
        ((condensedRingObj Λ B).obj.map h.op s) at hn
      have hm := regularPullbackIso_naturality_hom (upperStar Ab.{u + 1} h.left)
        (condensedRingObj Λ V.left) (condensedRingObj Λ W.left)
        (condensedPullbackHom Λ h.left)
        (multiplySection (condensedRingObj Λ V.left) ((sfbCoefficientSectionMap Λ V).hom s))
        (multiplySection (condensedRingObj Λ W.left) t) hp
      exact hm.trans (congrArg
        (fun t ↦ q.hom.hom ≫ (multiplySection (condensedRingObj Λ W.left) t).hom) hn)

end AlgebraicGeometry.ProEtale
