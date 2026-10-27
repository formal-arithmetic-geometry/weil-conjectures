/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.AlgebraicGeometry.SpaceFppfRingedComparison
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap

import Sheaf.AlgebraicGeometry.SpaceFppfQCohHigherVanishing
import Sheaf.CategoryTheory.RingedAcyclicResolutionDerivedMaps
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Flat-object comparison with one big-fppf resolution

Source: Stacks Project, More on Cohomology of Spaces, Tags 0DGN and 0DGP
(blueprint: lem-sfb-flat-object-fppf-derived-sections).

The auxiliary constructions retain the actual scheme charts, tensor pullback, and
restrictions of one resolution. The comparison is normalized by its derived unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Cache the standard abelian sheafification instance on the enlarged site.
Source: Stacks, Tag 03DA (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
instance flatObjectEnlargedHasSheafify (Y : AlgebraicSpace S) :
    HasSheafify Y.enlargedEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

/-- Global sections exist as the limit of the underlying abelian presheaf.
Source: Stacks, Tag 03F3 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
instance flatObjectEnlargedHasGlobalSections (Y : AlgebraicSpace S) :
    HasGlobalSectionsFunctor Y.enlargedEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

/-- The standard abelian structure, cached for the fixed enlarged site.
Source: Stacks, Tag 03DA (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
instance flatObjectEnlargedAbelian (Y : AlgebraicSpace S) :
    Abelian (Sheaf Y.enlargedEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance

/-- The ordinary abelian global-sections functor on the existing enlarged site.
Source: Stacks, Tag 03F3 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev flatObjectGlobalSections (Y : AlgebraicSpace S) :=
  Sheaf.Γ Y.enlargedEtaleTopology AddCommGrpCat.{u + 1}


/-- The global-sections functor is additive.
Source: Stacks, Tag 03F3 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
instance flatObjectGlobalSections_additive (Y : AlgebraicSpace S) :
    (flatObjectGlobalSections Y).Additive := inferInstance

/-- The equivalence already specified by the small presentation of the big site.
Source: Stacks, Tag 03Y8 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev SpaceFppfSite.presentationEquivalence (B : SpaceFppfSite X) : B.C ≌ Over X :=
  @Functor.asEquivalence _ _ _ _ B.inclusion
    { faithful := B.fullyFaithful.faithful
      full := B.fullyFaithful.full
      essSurj := B.essSurj }

/-- The ordinary section complex obtained by evaluating the single resolution.
Source: Stacks, Tag 0DGN (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev flatObjectEvaluation {B : SpaceFppfSite X} (R : SpaceFppfRings B) (T : B.C) :=
  SheafOfModules.toSheaf R.rings ⋙ sheafToPresheaf B.topology AddCommGrpCat.{u + 1} ⋙
    (evaluation B.Cᵒᵖ AddCommGrpCat.{u + 1}).obj (op T)

/-- The section complex before taking cohomology.
Source: Stacks, Tag 0DGN (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev flatObjectSectionComplex {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ) (T : B.C) :=
  ((flatObjectEvaluation R T).mapHomologicalComplex (.up ℤ)).obj J

/-- All evaluations of one complex, with exactly its own restriction maps.
Source: Stacks, Tags 0DGN and 0DGP
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectSectionDiagram {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ) :
    B.Cᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u + 1} ℤ where
  obj T := flatObjectSectionComplex R J T.unop
  map f :=
    { f := fun q ↦ (J.X q).val.presheaf.map f
      comm' := fun p q _ ↦ ((SheafOfModules.toSheaf R.rings).map (J.d p q)).hom.naturality f }
  map_id T := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact (J.X q).val.presheaf.map_id T
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact (J.X q).val.presheaf.map_comp f g

/-- Put each enlarged etale object into the same fixed big site.
Source: Stacks, Tags 03G1 and 0DGN
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectEnlargedInclusion (B : SpaceFppfSite X) (T : B.C) :
    (B.inclusion.obj T).left.EnlargedEtaleSite ⥤ B.C :=
  ObjectProperty.ι _ ⋙ Over.map (B.inclusion.obj T).hom ⋙ B.presentationEquivalence.inverse

/-- Restriction to the enlarged etale site before asserting the sheaf condition.
Source: Stacks, Tag 0DGN (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectEnlargedPresheaf {B : SpaceFppfSite X} (R : SpaceFppfRings B) (T : B.C) :=
  SheafOfModules.toSheaf R.rings ⋙ sheafToPresheaf B.topology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ _).obj (flatObjectEnlargedInclusion B T).op

/-- Restriction is additive, since it evaluates every section map unchanged.
Source: Stacks, Tag 0DGN (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
instance flatObjectEnlargedPresheaf_additive {B : SpaceFppfSite X}
    (R : SpaceFppfRings B) (T : B.C) : (flatObjectEnlargedPresheaf R T).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf R.rings ⋙
    sheafToPresheaf B.topology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ _).obj (flatObjectEnlargedInclusion B T).op).Additive)

/-- The actual etale base-change direct image is additive by precomposition.
Source: Stacks, Tag 03G2 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
instance flatObjectEnlargedDirectImage_additive {Y Z : AlgebraicSpace S} (f : Y ⟶ Z) :
    (enlargedDirectImage f AddCommGrpCat.{u + 1}).Additive where
  map_add := by intros; rfl

/-- Extend the original module by the recorded normalized equivalence, then lift
its abelian carriers into the common coefficient universe.
Source: Stacks, Tags 03G1 and 03DA
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectEnlargedCoefficients (Y : AlgebraicSpace S) :
    Y.Modules ⥤ Sheaf Y.enlargedEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEnlargedModuleEquivalence.{u, u} Y).inverse ⋙
    SheafOfModules.toSheaf Y.enlargedStructureSheaf ⋙
    sheafCompose Y.enlargedEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The representative of an enlarged chart maps to T through the specified counit.
Source: Stacks, Tag 03Y8 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectEnlargedChartArrow (B : SpaceFppfSite X) (T : B.C)
    (V : (B.inclusion.obj T).left.EnlargedEtaleSite) :
    (flatObjectEnlargedInclusion B T).obj V ⟶ T :=
  B.fullyFaithful.preimage (Over.homMk
    ((B.presentationEquivalence.counitIso.hom.app
      ((Over.map (B.inclusion.obj T).hom).obj V.obj)).left ≫ V.obj.hom)
    (by rw [Category.assoc]; exact Over.w (B.presentationEquivalence.counitIso.hom.app _)))

/-- The second projection of the actual fibre product in the one big site.
Source: Stacks, Tag 03G2 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectBaseChangeArrow (B : SpaceFppfSite X) {U T : B.C} (a : U ⟶ T)
    (V : (B.inclusion.obj T).left.EnlargedEtaleSite) :
    (flatObjectEnlargedInclusion B U).obj
        ((enlargedBaseChange (B.inclusion.map a).left).obj V) ⟶
      (flatObjectEnlargedInclusion B T).obj V :=
  B.presentationEquivalence.inverse.map (Over.homMk
    (ObjectProperty.homMk (Limits.pullback.snd (B.inclusion.map a).left.hom V.obj.hom.hom))
    (by
      apply ObjectProperty.hom_ext
      change Limits.pullback.snd (B.inclusion.map a).left.hom V.obj.hom.hom ≫
          (V.obj.hom.hom ≫ (B.inclusion.obj T).hom.hom) =
        Limits.pullback.fst (B.inclusion.map a).left.hom V.obj.hom.hom ≫
          (B.inclusion.obj U).hom.hom
      rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
      exact congrArg (fun k ↦ Limits.pullback.fst (B.inclusion.map a).left.hom
        V.obj.hom.hom ≫ k) (congrArg (fun k ↦ k.hom) (Over.w (B.inclusion.map a)))))

/-- Put the scheme chart V of T into B.
Source: Stacks, Tags 03G1 and 0DGN
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev flatObjectEtaleInclusion (B : SpaceFppfSite X) (T : B.C) :=
  enlargedSchemeInclusion (B.inclusion.obj T).left ⋙ flatObjectEnlargedInclusion B T

/-- The chart representative's actual projection to T.
Source: Stacks, Tag 03Y8 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev flatObjectChartProjection (B : SpaceFppfSite X) (T : B.C)
    (V : (B.inclusion.obj T).left.EtaleSite) :=
  (B.inclusion.map (flatObjectEnlargedChartArrow B T
    ((enlargedSchemeInclusion _).obj V))).left

/-- Tensor associativity and the triangle of the canonical chart projection.
Source: Stacks, Tag 03D7 (blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectChartTensorIso (B : SpaceFppfSite X) (T : B.C)
    (V : (B.inclusion.obj T).left.EtaleSite) :
    moduleTensorPullback (B.inclusion.obj T).hom ⋙
        moduleTensorPullback (flatObjectChartProjection B T V) ≅
      moduleTensorPullback (B.inclusion.obj ((flatObjectEtaleInclusion B T).obj V)).hom :=
  moduleTensorComposition _ _ ≪≫ eqToIso (congrArg moduleTensorPullback
    (Over.w (B.inclusion.map
      (flatObjectEnlargedChartArrow B T ((enlargedSchemeInclusion _).obj V)))))

/-- A derived-section comparison fixed by the resolution augmentation and derived unit.
This factors the categorical part without changing any of its normalization equations.
Source: Stacks, Tags 0DGN and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
structure FlatObjectSectionDerivedComparison
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    (G : A ⥤ AddCommGrpCat.{u + 1}) [G.Additive]
    (N : A) (K : CochainComplex A ℤ)
    (r : (CochainComplex.singleFunctor A 0).obj N ⟶ K)
    (L : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (e : (G.mapHomologicalComplex (.up ℤ)).obj K ≅ L) where
  derived : DerivedCategory A ⥤ DerivedCategory AddCommGrpCat.{u + 1}
  unit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ derived
  universal : derived.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  comparison : derived.obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj N)) ≅
    DerivedCategory.Q.obj L
  comparison_normalization : comparison.inv ≫ derived.map (DerivedCategory.Q.map r) =
    DerivedCategory.Q.map e.inv ≫ unit.app K

/-- Resolution comparison data with abstract categories, retaining the actual
restriction and global-sections functors as parameters.
Source: Stacks, Tags 0DGN, 0DGP and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
structure FlatObjectSectionModelDataCore
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Preadditive B] [HasZeroObject B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    (G : A ⥤ AddCommGrpCat.{u + 1}) (P : A ⥤ B) [G.Additive] [P.Additive]
    (N : A) (L : CochainComplex B ℤ) (out : CochainComplex AddCommGrpCat.{u + 1} ℤ) where
  complex : CochainComplex A ℤ
  presheafIso : (P.mapHomologicalComplex (.up ℤ)).obj complex ≅ L
  augmentation : (CochainComplex.singleFunctor A 0).obj N ⟶ complex
  sectionsIso : (G.mapHomologicalComplex (.up ℤ)).obj complex ≅ out
  derivedData : FlatObjectSectionDerivedComparison G N complex augmentation out sectionsIso

/-- The actual enlarged-etale resolution data in the one fixed big site.
Source: Stacks, Tags 0DGN and 0DGP
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev FlatObjectFppfSectionModelData {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (_Fa : SheafOfModules.{u + 1} R.rings)
    (_eFa : IsSpaceFppfSectionExtension R M _Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (_ι : (CochainComplex.singleFunctor _ 0).obj _Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})] :=
  FlatObjectSectionModelDataCore (flatObjectGlobalSections (B.inclusion.obj T).left)
    (sheafToPresheaf _ AddCommGrpCat.{u + 1})
    ((flatObjectEnlargedCoefficients _).obj
      ((moduleTensorPullback (B.inclusion.obj T).hom).obj M))
    (((flatObjectEnlargedPresheaf R T).mapHomologicalComplex (.up ℤ)).obj J)
    (flatObjectSectionComplex R J T)

/- The nonnegative resolution, tensor augmentation and section-projection conditions.
All conditions of the original per-object comparison are retained explicitly.
Source: Stacks, Tags 0DGN and 0DGP
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
/-- Clause 1 of the normalized model conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfSectionModelNonnegative {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    (d : FlatObjectFppfSectionModelData R M Fa eFa J ι T) : Prop :=
  d.complex.IsStrictlyGE 0

/-- Clause 2 of the normalized model conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfSectionModelQuasiIso {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    (d : FlatObjectFppfSectionModelData R M Fa eFa J ι T) : Prop :=
  QuasiIso d.augmentation

/-- Clause 3 of the normalized model conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfSectionModelTensorAugmentation {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    (d : FlatObjectFppfSectionModelData R M Fa eFa J ι T) : Prop :=
  ∀ (V : (B.inclusion.obj T).left.EtaleSite)
      (x : ((moduleTensorPullback (B.inclusion.obj T).hom).obj M).val.obj (op V)),
    ∃ s : Fa.val.obj (op ((flatObjectEtaleInclusion B T).obj V)),
      (∀ q : ModuleChart (flatObjectChartProjection B T V) V,
        ((eFa.sections ((flatObjectEtaleInclusion B T).obj V)) s).val (op q.left) =
          ((flatObjectChartTensorIso B T V).hom.app M).val.app (op q.left)
            (moduleTensorSection (flatObjectChartProjection B T V)
              ((moduleTensorPullback (B.inclusion.obj T).hom).obj M) V q 1 x)) ∧
      (d.presheafIso.hom.f 0).app (op ((enlargedSchemeInclusion _).obj V))
          ((d.augmentation.f 0).hom.app (op ((enlargedSchemeInclusion _).obj V))
            (ULift.up (((smallEnlargedModuleEquivalence.{u, u} _).counitIso.inv.app
              ((moduleTensorPullback (B.inclusion.obj T).hom).obj M)).val.app (op V) x))) =
        (ι.f 0).val.app (op ((flatObjectEtaleInclusion B T).obj V)) s

/-- Clause 4 of the normalized model conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfSectionModelSectionProjections {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    (d : FlatObjectFppfSectionModelData R M Fa eFa J ι T) : Prop :=
  ∀ (q : ℤ)
      (V : (B.inclusion.obj T).left.EnlargedEtaleSite),
    d.sectionsIso.hom.f q ≫
        (J.X q).val.presheaf.map (flatObjectEnlargedChartArrow B T V).op =
      Sheaf.ΓRes (d.complex.X q) (op V) ≫ (d.presheafIso.hom.f q).app (op V)

/-- All 4 explicit canonicality clauses, conjoined without weakening any condition.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfSectionModelConditions {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    (d : FlatObjectFppfSectionModelData R M Fa eFa J ι T) : Prop :=
  FlatObjectFppfSectionModelNonnegative R M Fa eFa J ι T d ∧
  FlatObjectFppfSectionModelQuasiIso R M Fa eFa J ι T d ∧
  FlatObjectFppfSectionModelTensorAugmentation R M Fa eFa J ι T d ∧
  FlatObjectFppfSectionModelSectionProjections R M Fa eFa J ι T d

/-- A normalized nonnegative etale resolution with its canonical derived comparison.
Its subtype property retains the tensor augmentation and global-section projections.
Source: Stacks, Tags 0DGN and 0DGP
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev FlatObjectFppfSectionModel {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    (T : B.C) [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})] :=
  {d : FlatObjectFppfSectionModelData R M Fa eFa J ι T //
    FlatObjectFppfSectionModelConditions R M Fa eFa J ι T d}

/-- The pulled-back coefficient sheaf in the faithful common abelian universe.
Source: Stacks, Tags 03G1 and 0DGN
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev flatObjectCoefficient {B : SpaceFppfSite X} (M : X.Modules) (T : B.C) :=
  (flatObjectEnlargedCoefficients _).obj ((moduleTensorPullback (B.inclusion.obj T).hom).obj M)

/-- A scheme section in the normalized enlarged coefficient sheaf.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectCoefficientSection (Y : AlgebraicSpace S) (N : Y.Modules)
    (V : Y.EtaleSite) (x : N.val.obj (op V)) :
    ((flatObjectEnlargedCoefficients Y).obj N).obj.obj
      (op ((enlargedSchemeInclusion Y).obj V)) :=
  ULift.up (((smallEnlargedModuleEquivalence.{u, u} Y).counitIso.inv.app N).val.app (op V) x)

/-- The tensor associator along an arrow over X, with its specified triangle.
Source: Stacks, Tag 03D7
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def flatObjectArrowTensorIso (B : SpaceFppfSite X) {U T : B.C} (a : U ⟶ T) :
    moduleTensorPullback (B.inclusion.obj T).hom ⋙
        moduleTensorPullback (B.inclusion.map a).left ≅
      moduleTensorPullback (B.inclusion.obj U).hom :=
  moduleTensorComposition _ _ ≪≫ eqToIso (congrArg moduleTensorPullback
    (Over.w (B.inclusion.map a)))

/-- The canonical derived-restriction square with Rf and kappa fixed by derived units.
The arrow is explicitly RG of the localized degree-zero coefficient map followed by
its derived-pushforward unit, then kappa. This is the RG/Rf/kappa formula of the
acyclic-resolution derived-map theorem, with independent sheaf-category universes.
Source: Stacks, Tags 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectDerivedRestrictionSquare
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    (F : A ⥤ B) (G : B ⥤ AddCommGrpCat.{u + 1}) (H : A ⥤ AddCommGrpCat.{u + 1})
    [F.Additive] [G.Additive] [H.Additive]
    (RG : DerivedCategory B ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (RH : DerivedCategory A ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (ηH : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)
    (t : F ⋙ G ≅ H) {M : B} {N : A} (φ : M ⟶ F.obj N)
    (P Q : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (cM : RG.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor B 0).obj M)) ≅
      DerivedCategory.Q.obj P)
    (cN : RH.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj N)) ≅
      DerivedCategory.Q.obj Q) (r : P ⟶ Q) : Prop :=
  ∃ (Rf : DerivedCategory A ⥤ DerivedCategory B)
    (ηf : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rf),
    Rf.IsRightDerivedFunctor ηf (HomologicalComplex.quasiIso A (.up ℤ)) ∧
    ∃ κ : Rf ⋙ RG ≅ RH,
      (∀ K : CochainComplex A ℤ,
        ηG.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ RG.map (ηf.app K) ≫
            κ.hom.app (DerivedCategory.Q.obj K) =
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app K) ≫
            ηH.app K) ∧
      RG.map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor B 0).map φ ≫
            (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app N) ≫
          ηf.app ((CochainComplex.singleFunctor A 0).obj N)) ≫
        κ.hom.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj N)) ≫
        cN.hom = cM.hom ≫ DerivedCategory.Q.map r

/-- Actual coefficient, chain and section maps in abstract categories.
The canonicality conditions are imposed separately and retain all their equations.
Source: Stacks, Tags 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev FlatObjectTransitionDataCore
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Preadditive A] [Preadditive B]
    (F : A ⥤ B) (G : B ⥤ AddCommGrpCat.{u + 1}) (H : A ⥤ AddCommGrpCat.{u + 1})
    [F.Additive] [G.Additive] [H.Additive]
    (M : B) (N : A) (KT : CochainComplex B ℤ) (KU : CochainComplex A ℤ) :=
  (M ⟶ F.obj N) ×
    (KT ⟶ (F.mapHomologicalComplex (.up ℤ)).obj KU) ×
    (F ⋙ G ≅ H) ×
    ((G.mapHomologicalComplex (.up ℤ)).obj KT ⟶
      (H.mapHomologicalComplex (.up ℤ)).obj KU)

/-- The actual coefficient, chain and section maps for the specified space arrow.
Source: Stacks, Tags 0DGP and 0D6E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev FlatObjectFppfTransitionData {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U) :=
  FlatObjectTransitionDataCore
    (enlargedDirectImage (B.inclusion.map a).left AddCommGrpCat.{u + 1})
    (flatObjectGlobalSections (B.inclusion.obj T).left)
    (flatObjectGlobalSections (B.inclusion.obj U).left)
    (flatObjectCoefficient M T) (flatObjectCoefficient M U) KT.complex KU.complex

/- The full tensor, augmentation, section and derived naturality conditions.
They are factored as a predicate to avoid regenerating large induction principles;
every equality is the explicit canonicality condition, not an extra hypothesis.
Source: Stacks, Tags 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
/-- Clause 1 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionTensorCoefficient {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  ∀ (V : (B.inclusion.obj T).left.EtaleSite)
      (q : ModuleChart (B.inclusion.map a).left V)
      (x : ((moduleTensorPullback (B.inclusion.obj T).hom).obj M).val.obj (op V)),
    (flatObjectCoefficient M U).obj.map
        (enlargedChartLift (B.inclusion.map a).left q.left V q.hom.left q.hom.w).op
        (d.1.hom.app (op ((enlargedSchemeInclusion _).obj V))
          (flatObjectCoefficientSection _ _ V x)) =
      flatObjectCoefficientSection _ _ q.left
        (((flatObjectArrowTensorIso B a).hom.app M).val.app (op q.left)
          (moduleTensorSection (B.inclusion.map a).left
            ((moduleTensorPullback (B.inclusion.obj T).hom).obj M) V q 1 x))

/-- Clause 2 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionAugmentation {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  KT.augmentation ≫ d.2.1 =
    (CochainComplex.singleFunctor _ 0).map d.1 ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (enlargedDirectImage (B.inclusion.map a).left AddCommGrpCat.{u + 1})
        (.up ℤ) 0).inv.app (flatObjectCoefficient M U) ≫
      ((enlargedDirectImage (B.inclusion.map a).left AddCommGrpCat.{u + 1}).mapHomologicalComplex
         (.up ℤ)).map KU.augmentation

/-- Clause 3 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionRestriction {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  ∀ (q : ℤ) (V : (B.inclusion.obj T).left.EnlargedEtaleSite),
    (KT.presheafIso.hom.f q).app (op V) ≫
        (J.X q).val.presheaf.map (flatObjectBaseChangeArrow B a V).op =
      (d.2.1.f q).hom.app (op V) ≫ (KU.presheafIso.hom.f q).app
        (op ((enlargedBaseChange (B.inclusion.map a).left).obj V))

/-- Clause 4 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionSectionTransport {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  ∀ (A : Sheaf (B.inclusion.obj U).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})
      (V : (B.inclusion.obj T).left.EnlargedEtaleSite),
    d.2.2.1.inv.app A ≫
        Sheaf.ΓRes ((enlargedDirectImage (B.inclusion.map a).left
          AddCommGrpCat.{u + 1}).obj A) (op V) =
      Sheaf.ΓRes A (op ((enlargedBaseChange (B.inclusion.map a).left).obj V))

/-- Clause 5 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionSectionMap {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  d.2.2.2 =
    ((flatObjectGlobalSections (B.inclusion.obj T).left).mapHomologicalComplex (.up ℤ)).map
        d.2.1 ≫
      (Functor.mapHomologicalComplexCompIso d.2.2.1 (.up ℤ)).hom.app KU.complex

/-- Clause 6 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionSectionIdentification {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  KT.sectionsIso.hom ≫ (flatObjectSectionDiagram R J).map a.op =
    d.2.2.2 ≫ KU.sectionsIso.hom

/-- Clause 7 of the normalized transition conditions, with its full canonical formula.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionDerivedNaturality {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  FlatObjectDerivedRestrictionSquare
    (enlargedDirectImage (B.inclusion.map a).left AddCommGrpCat.{u + 1})
    (flatObjectGlobalSections (B.inclusion.obj T).left)
    (flatObjectGlobalSections (B.inclusion.obj U).left)
    KT.derivedData.derived KU.derivedData.derived
    KT.derivedData.unit KU.derivedData.unit
    d.2.2.1 d.1 (flatObjectSectionComplex R J T)
    (flatObjectSectionComplex R J U) KT.derivedData.comparison KU.derivedData.comparison
    ((flatObjectSectionDiagram R J).map a.op)

/-- All 7 explicit canonicality clauses, conjoined without weakening any condition.
Source: Stacks, Tags 0DGN, 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfTransitionConditions {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U)
    (d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU) : Prop :=
  FlatObjectFppfTransitionTensorCoefficient R M Fa eFa J ι a KT KU d ∧
  FlatObjectFppfTransitionAugmentation R M Fa eFa J ι a KT KU d ∧
  FlatObjectFppfTransitionRestriction R M Fa eFa J ι a KT KU d ∧
  FlatObjectFppfTransitionSectionTransport R M Fa eFa J ι a KT KU d ∧
  FlatObjectFppfTransitionSectionMap R M Fa eFa J ι a KT KU d ∧
  FlatObjectFppfTransitionSectionIdentification R M Fa eFa J ι a KT KU d ∧
  FlatObjectFppfTransitionDerivedNaturality R M Fa eFa J ι a KT KU d

/-- A coefficient-compatible transition with canonical derived restriction.
The conditions contain the tensor-normalized degree-zero map, its augmentation square,
the Gamma-of-transition section map, and the unit-normalized derived naturality square.
Source: Stacks, Tags 0DGP, 0D6E and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
abbrev FlatObjectFppfTransition {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    {U T : B.C} (a : U ⟶ T)
    (KT : FlatObjectFppfSectionModelData R M Fa eFa J ι T)
    (KU : FlatObjectFppfSectionModelData R M Fa eFa J ι U) :=
  {d : FlatObjectFppfTransitionData R M Fa eFa J ι a KT KU //
    FlatObjectFppfTransitionConditions R M Fa eFa J ι a KT KU d}

/-- Simultaneous resolution models whose arrows are global sections of the chosen
coefficient-compatible transitions, with their face-compatible comparison zigzag.
Source: Stacks, Tags 0DGP and 0D6E
(blueprint: lem-sfb-flat-object-fppf-derived-sections). -/
def FlatObjectFppfDiagramModel {B : SpaceFppfSite X} (R : SpaceFppfRings B)
    (M : X.Modules) (Fa : SheafOfModules.{u + 1} R.rings)
    (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J)
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})]
    (models : ∀ T : B.C, MapIsFlat (B.inclusion.obj T).hom →
      FlatObjectFppfSectionModel R M Fa eFa J ι T)
    (transitions : ∀ (U T : B.C) (a : U ⟶ T)
      (hU : MapIsFlat (B.inclusion.obj U).hom) (hT : MapIsFlat (B.inclusion.obj T).hom),
      MapIsFlat (B.inclusion.map a).left →
        FlatObjectFppfTransition R M Fa eFa J ι a (models T hT).val (models U hU).val)
    {I : Type v} [SmallCategory I] (D : I ⥤ B.Cᵒᵖ)
    (hD : ∀ i : I, MapIsFlat (B.inclusion.obj (D.obj i).unop).hom)
    (hA : ∀ {i j : I} (a : i ⟶ j),
      MapIsFlat (B.inclusion.map (D.map a).unop).left) : Prop :=
  ∃ (complex : I ⥤ CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (comparison : complex ≅ D ⋙ flatObjectSectionDiagram R J),
    (∀ i : I, (complex.obj i).IsStrictlyGE 0) ∧
    ∃ identification : ∀ i : I, complex.obj i ≅
        ((flatObjectGlobalSections (B.inclusion.obj (D.obj i).unop).left).mapHomologicalComplex
           (.up ℤ)).obj (models (D.obj i).unop (hD i)).val.complex,
      (∀ i : I,
        (identification i).hom ≫ (models (D.obj i).unop (hD i)).val.sectionsIso.hom =
          comparison.hom.app i) ∧
      ∀ {i j : I} (a : i ⟶ j),
        (identification i).hom ≫
            (transitions _ _ (D.map a).unop (hD j) (hD i) (hA a)).val.2.2.2 =
          complex.map a ≫ (identification j).hom

/-- The normalized tensor-pullback section presheaf is an fppf module sheaf.
Source: Stacks, Tag 0DGN(1),(3)
(blueprint: lem-sfb-flat-object-fppf-derived-sections).
Proof: reinterpret local sections as maps O to the pulled-back quasi-coherent module.
Full faithfulness in quasi-coherent fppf descent glues the maps uniquely. The same
uniqueness gives the addition, scalar and restriction formulas. Tensor associativity
and its units supply the composition and identity normalization. -/
theorem flat_object_fppf_section_extension
    {S : Scheme.{u}} (X : AlgebraicSpace S) (B : SpaceFppfSite X)
    (R : SpaceFppfRings B) (M : X.Modules) (hM : M.IsQuasicoherent) :
    ∃ Fa : SheafOfModules.{u + 1} R.rings,
      Nonempty (IsSpaceFppfSectionExtension R M Fa) := by
  sorry

/-- The single-resolution derived comparison and simultaneous flat-diagram models.
Source: Stacks, Tags 0DGN(1),(3),(6),(7), 0DGP and 015E
(blueprint: lem-sfb-flat-object-fppf-derived-sections).

Proof:
1. Quasi-coherent fppf descent glues maps O to h-star M, hence the section extension;
   tensor pullback preserves quasi-coherence by
   lem-sfb-space-module-pullback-quasicoherent. Tensor associativity identifies its
   restriction to the slice over T with the extension of h-star M.
2. Restrict J to this slice. The exact localization adjunction of
   lem-pur-site-restriction-module-adjunction-exact and the injective-preservation
   theorem lem-sp-right-adjoint-preserves-injectives make it an injective resolution.
   Enough injectives follow from lem-weil-pbc-small-module-diagrams-grothendieck
   and lem-sp-grothendieck-enough-injectives.
3. Restrict to the enlarged etale site. Terms on V are J(V). The positive higher
   images vanish by lem-sfb-space-fppf-qcoh-higher-vanishing. The localization clause
   of lem-trf-space-enlarged-etale-ringed-site-model identifies etale tensor pullback
   with restriction in degree zero, hence the augmentation is a quasi-isomorphism.
4. Direct images of injectives are totally acyclic by
   lem-sfb-injective-pushforward-totally-acyclic. The acyclic-resolution computation
   lem-sfb-ringed-acyclic-resolution-derived-maps gives the unit-normalized derived
   comparison. Its sections are J(T), with exactly the displayed chart restrictions.
   The recorded small/enlarged equivalence retains the original module; lifting
   its abelian coefficients faithfully places it in the common coefficient universe.
5. For each flat U to T, restriction in J on V to U times_T V defines the chain
   transition. Its augmentation is the usual tensor pullback by the section-extension
   normalization and tensor associativity. The same acyclic-resolution derived-map
   theorem supplies Rf and kappa normalized by the derived units. Localize the
   tensor coefficient map and apply the Rf unit followed by kappa; its square with
   the two comparisons equals Q of the same J restriction. This is the displayed
   derived_naturality equation, not just naturality on cohomology.
6. Restrictions in one presheaf complex are strictly functorial. For every small
   diagram, including an augmentation object, use its section complexes as one strict
   diagram. Choose the transitions once for all arrows. Their sectionMap is Gamma
   of the chosen transition under the projection-normalized sectionTransport.
   Each diagram map is identified with that sectionMap, including its augmentation.
   The sectionsIso comparisons give a natural one-step zigzag of
   quasi-isomorphisms. Every component is zero below zero. This includes X/X,
   identity arrows and maps to X. No quasi-compactness, separation or finite bound
   on the diagram is used. -/
theorem flat_object_fppf_derived_sections
    {S : Scheme.{u}} (X : AlgebraicSpace S) (B : SpaceFppfSite X)
    (R : SpaceFppfRings B) (M : X.Modules) (hM : M.IsQuasicoherent)
    (Fa : SheafOfModules.{u + 1} R.rings) (eFa : IsSpaceFppfSectionExtension R M Fa)
    (J : CochainComplex (SheafOfModules.{u + 1} R.rings) ℤ) [J.IsStrictlyGE 0]
    [∀ q : ℤ, Injective (J.X q)]
    (ι : (CochainComplex.singleFunctor _ 0).obj Fa ⟶ J) [QuasiIso ι]
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]
    [∀ T : B.C, HasDerivedCategory.{w}
      (Sheaf (B.inclusion.obj T).left.enlargedEtaleTopology AddCommGrpCat.{u + 1})] :
    ∃ models : ∀ (T : B.C), MapIsFlat (B.inclusion.obj T).hom →
          FlatObjectFppfSectionModel R M Fa eFa J ι T,
      ∃ transitions : ∀ (U T : B.C) (a : U ⟶ T)
          (hU : MapIsFlat (B.inclusion.obj U).hom)
          (hT : MapIsFlat (B.inclusion.obj T).hom),
          MapIsFlat (B.inclusion.map a).left →
            FlatObjectFppfTransition R M Fa eFa J ι a (models T hT).val (models U hU).val,
        ∀ (I : Type v) [SmallCategory I] (D : I ⥤ B.Cᵒᵖ)
          (hD : ∀ i : I, MapIsFlat (B.inclusion.obj (D.obj i).unop).hom)
          (hA : ∀ {i j : I} (a : i ⟶ j),
            MapIsFlat (B.inclusion.map (D.map a).unop).left),
          FlatObjectFppfDiagramModel R M Fa eFa J ι models transitions D hD hA := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
