/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingCompositionCancelledEquation
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralScalarReindexingComposition
import WeilConjectures.SmoothPurity.Common.CommonStageCompositorIntegralNormalization
import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
import WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponent

/-! # Finite-stage cancelled composition

Finite localization transports and completion-unit identifications reduce the
realization composition calculation to its ambient balanced-scalar square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCoefficientLinear
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
  GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  Scheme.residueField completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  sfRationalScalarExtension rationalPullbackScalarComparison sfRationalScalarComp

private abbrev stageObject (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (X : Scheme.{u}) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⥤
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E

private def reindexComp (C : FamilyCore l D)
    (T U V : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h : U.base.left ≅ V.base.left) :
    derivedPull l T.base.left (g ≪≫ h).hom (C.ring T V (g ≪≫ h)) ≅
      derivedPull l U.base.left h.hom (C.ring U V h) ⋙
        derivedPull l T.base.left g.hom (C.ring T U g) :=
  Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem rationalPull_object {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) f).obj N =
      (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
          ((constructibleIntegralPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) f).obj N.obj) := by
  simpa only [rationalDerivedPullback] using
    (rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) f).exists.choose_spec.2.1
        N

private def stagePullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (commonStageDerivedPullback l (PadicAlgCl l) f).obj ((stageObject l E Y).obj K) ≅
      (stageObject l E X).obj ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) f).obj K) :=
  eqToIso (zlStagePull_eq l (PadicAlgCl l) f E K)

attribute [local irreducible] constructibleIntegralPullback

attribute [local irreducible] stagePullIso

private theorem map_heq {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X Y X' Y' : A} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem transport_heq {A : Type*} [Category* A]
    {X Y X' Y' : A} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    f ≫ eqToHom hy = eqToHom hx ≫ g := by
  cases hx
  cases hy
  cases h
  simp

private theorem stagePullIso_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Z) :
    (pullbackTensorCommonComposition l (PadicAlgCl l) g f
        ((stageObject l E Z).obj K)).hom ≫
      (commonStageDerivedPullback l (PadicAlgCl l) f).map (stagePullIso l g E K).hom ≫
      (stagePullIso l f E ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K)).hom =
    (stagePullIso l (f ≫ g) E K).hom ≫
      (stageObject l E X).map ((pullbackTensorIntegralComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g f).hom.app K) := by
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let M := (stageObject l E Z).obj K
  have hobj {V W : Scheme.{u}} (h : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)] (N) :
      (rationalDerivedPullback l A h).obj N =
        (sfRationalConstructibleLocalization l A V).obj
          ((constructibleIntegralPullback l A h).obj N.obj) :=
    rationalPull_object l h E N
  have hb : (rationalDerivedPullback l A f).obj
      ((rationalDerivedPullback l A g).obj M.obj) =
      (sfRationalConstructibleLocalization l A X).obj
        ((constructibleIntegralPullback l A f).obj
          ((constructibleIntegralPullback l A g).obj K)) :=
    (hobj f _).trans (congrArg (fun N ↦
      (sfRationalConstructibleLocalization l A X).obj
        ((constructibleIntegralPullback l A f).obj N.obj)) (hobj g M.obj))
  have hc := (commonStageCompositor_integral l (PadicAlgCl l) f g M).trans
    (map_heq
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E) (hobj (f ≫ g) M.obj) hb
      (pullbackTensorRationalComposition_existsUnique l A g f M.obj).exists.choose_spec)
  unfold stagePullIso
  dsimp only [eqToIso.hom]
  simp only [eqToHom_map, eqToHom_trans]
  apply transport_heq _ _ hc

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback
  ObjectProperty.lift ObjectProperty.ι Functor.comp inducedFunctor

private def stageReindexIso (C : FamilyCore l D)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left) :
    letI := (C.data T).units
    letI := (C.data U).units
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).obj
        (((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom).obj K).obj) ≅
      (derivedPull l T.base.left g.hom (C.ring T U g)).obj
        ((pbcDerivedExtend (coefficientMap l U.base.left (C.data U).realization E)).obj K.obj) :=
  (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).mapIso
      (podCompletedToTowerIso l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom K).symm ≪≫
    ((C.integral T U g E).derived.app K.obj).symm

private theorem stageReindexIso_hom (C : FamilyCore l D)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left) :
    letI := (C.data T).units
    letI := (C.data U).units
    (stageReindexIso l D C T U g E K).hom =
      (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
          (podCompletedToTowerIso l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom K).inv ≫
        (C.integral T U g E).derived.inv.app K.obj := rfl

attribute [local implicit_reducible] ordinary

attribute [local irreducible] stageReindexIso reindexComp derivedPull
  podCompletedDerivedInverseImage integralDerivedPullback

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] derivedPull reindexComp

private theorem completion_square {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (L : A ⥤ B) (R : C ⥤ D) (G : D ⥤ B) (P : C ⥤ A)
    {X X' : C} {Y Y' Z : A} {N : B} {W : D}
    (t : X ≅ X') (s : P.obj X' ≅ Y') (v : Y ≅ Z)
    (j : Y ⟶ P.obj X) (k : Z ⟶ Y')
    (a : L.obj Y ⟶ N) (d : N ⟶ G.obj W)
    (b0 : L.obj (P.obj X) ⟶ G.obj (R.obj X))
    (b1 : L.obj (P.obj X') ⟶ G.obj (R.obj X')) (c : R.obj X ⟶ W)
    (hk : k = v.inv ≫ j ≫ P.map t.hom ≫ s.hom)
    (hn : L.map (P.map t.hom) ≫ b1 = b0 ≫ G.map (R.map t.hom))
    (hs : a ≫ d = L.map j ≫ b0 ≫ G.map c) :
    L.map v.inv ≫ a ≫ d =
      L.map k ≫ L.map s.inv ≫ b1 ≫ G.map (R.map t.inv ≫ c) := by
  rw [hk, hs]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
  rw [reassoc_of% hn]
  simp only [← G.map_comp_assoc, ← R.map_comp, Iso.hom_inv_id,
    R.map_id, G.map_id, Category.id_comp]

private theorem stageReindexIso_composition (C : FamilyCore l D)
    (T U V : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h : U.base.left ≅ V.base.left)
    (hs : ∀ (M : modules l V.base.left (C.data V).realization) (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left) :
    letI := (C.data T).units
    letI := (C.data U).units
    letI := (C.data V).units
    (stageReindexIso l D C T V (g ≪≫ h) E K).hom ≫
      (reindexComp l D C T U V g h).hom.app
          ((pbcDerivedExtend (coefficientMap l V.base.left (C.data V).realization E)).obj K.obj) =
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
        (((pullbackTensorIntegralComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          h.hom g.hom).hom.app K).hom) ≫
      (stageReindexIso l D C T U g E ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K)).hom ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        (stageReindexIso l D C U V h E K).hom := by
  let := (C.data T).units
  let := (C.data U).units
  let := (C.data V).units
  let L := pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)
  let R := pbcDerivedExtend (coefficientMap l U.base.left (C.data U).realization E)
  let G := derivedPull l T.base.left g.hom (C.ring T U g)
  let P := podCompletedDerivedInverseImage l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom
  have hc := eq_of_heq (podIntegralPullbackComp_normalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom g.hom K)
  have hn := (C.integral T U g E).derived.inv.naturality
    (podCompletedToTowerIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom K).hom
  dsimp only [Functor.comp_map] at hn
  have hh := completion_square L R G P
    (podCompletedToTowerIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom K)
    (podCompletedToTowerIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom
      ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K))
    (podCompletedToTowerIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) (g.hom ≫ h.hom) K)
    ((podCompletedDerivedComp l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
      h.hom g.hom).hom.app K.obj)
    (((pullbackTensorIntegralComposition l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
      h.hom g.hom).hom.app K).hom)
    ((C.integral T V (g ≪≫ h) E).derived.inv.app K.obj)
    ((reindexComp l D C T U V g h).hom.app
        ((pbcDerivedExtend (coefficientMap l V.base.left (C.data V).realization E)).obj K.obj))
    ((C.integral T U g E).derived.inv.app
      ((podCompletedDerivedInverseImage l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K.obj))
    ((C.integral T U g E).derived.inv.app
      ((integralDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K.obj))
    ((C.integral U V h E).derived.inv.app K.obj)
    hc hn (integralScalarReindexing_composition l D C T U V g h hs E K.obj)
  simp only [stageReindexIso_hom, Category.assoc]
  dsimp only [L, R, G, Iso.trans_hom] at hh ⊢
  exact hh

private def stageRealizationIso (C : FamilyCore l D) (T : GeometricSpace D)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) T.base.left) :
    (ordinary l T.base.left (C.data T).realization).obj ((stageObject l E T.base.left).obj K) ≅
      (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).obj K.obj :=
  ((C.data T).realization.integral E).app K

private theorem map_cast_comp_heq {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {X Y : A} (p : X = Y) {Z : B} (t : F.obj Y ⟶ Z) :
    HEq (F.map (eqToIso p).hom ≫ t) t := by
  cases p
  simp

private theorem map_map_cast_comp_heq {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (I : A ⥤ B) (F : B ⥤ C) {X Y : A} (p : X = Y)
    {Z : C} (t : F.obj (I.obj Y) ⟶ Z) :
    HEq (F.map (I.map (eqToIso p).hom) ≫ t) t := by
  cases p
  simp

private theorem stage_normalization (C : FamilyCore l D)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (hn : letI := (C.data T).units
      letI := (C.data U).units
      integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
        (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left) :
    letI := (C.data T).units
    letI := (C.data U).units
    (C.comparison T U g).hom.app ((stageObject l E U.base.left).obj K) =
      (ordinary l T.base.left (C.data T).realization).map (stagePullIso l g.hom E K).hom ≫
        (stageRealizationIso l D C T E ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom).obj K)).hom ≫
        (stageReindexIso l D C T U g E K).hom ≫
        (derivedPull l T.base.left g.hom (C.ring T U g)).map
          (stageRealizationIso l D C U E K).inv := by
  let := (C.data T).units
  let := (C.data U).units
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := T.base.left) E
  let F := ordinary l T.base.left (C.data T).realization
  let tail := ((C.data T).realization.integral E).hom.app
      ((constructibleIntegralPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom).obj K) ≫
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
      (podCompletedToTowerIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom K).inv ≫
    (C.integral T U g E).derived.inv.app K.obj ≫
    (derivedPull l T.base.left g.hom (C.ring T U g)).map
      (((C.data U).realization.integral E).inv.app K)
  have h1 := (hn K).trans (map_cast_comp_heq F
    (commonStageDerivedPullback_object_representation l (PadicAlgCl l) g.hom
      ((stageObject l E U.base.left).obj K)) _)
  have h2 : HEq ((C.comparison T U g).hom.app ((stageObject l E U.base.left).obj K))
      tail := h1.trans (map_map_cast_comp_heq I F
        (rationalPull_object l g.hom E
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
            U.base.left).obj K)) tail)
  apply eq_of_heq
  apply h2.trans
  unfold stagePullIso
  have he := (map_cast_comp_heq F
    (zlStagePull_eq l (PadicAlgCl l) g.hom E K) tail).symm
  simp only [stageReindexIso_hom]
  dsimp only [tail, F, stageObject, stagePullIso, stageRealizationIso,
    Iso.app, ordinary, Functor.comp] at he ⊢
  simp only [Category.assoc] at he ⊢
  exact he

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] derivedPull reindexComp

private theorem assembly_square {B C D : Type*}
    [Category* B] [Category* C] [Category* D]
    (G : C ⥤ B) (H : D ⥤ C) (J : D ⥤ B) (d : J ≅ H ⋙ G)
    {X Y P Q R S T : B} {m0 m1 m2 : C} {n0 n1 : D}
    (v : n0 ≅ n1) (t : m1 ≅ m2)
    (q : X ⟶ R) (r : R ⟶ T) (j : T ⟶ J.obj n1)
    (c : X ⟶ Y) (f : Y ⟶ P) (p : P ⟶ Q) (k : R ⟶ Q)
    (s : Q ⟶ S) (a : T ⟶ S) (b : S ⟶ G.obj m2)
    (bh : m2 ⟶ H.obj n1) (e : m0 ⟶ m1)
    (aj : X ⟶ J.obj n0) (ag : Y ⟶ G.obj m0) (ag' : P ⟶ G.obj m1)
    (ah : m0 ⟶ H.obj n0)
    (hc : c ≫ f ≫ p = q ≫ k) (hr : k ≫ s = r ≫ a)
    (hb : j ≫ d.hom.app n1 = a ≫ b ≫ G.map bh)
    (hj : aj = q ≫ r ≫ j ≫ J.map v.inv)
    (hg : ag' = p ≫ s ≫ b ≫ G.map t.inv)
    (hh : ah = e ≫ t.hom ≫ bh ≫ H.map v.inv)
    (hn : f ≫ ag' = ag ≫ G.map e) :
    aj ≫ d.hom.app n0 = c ≫ ag ≫ G.map ah := by
  rw [hj, hh]
  simp only [Functor.map_comp, Category.assoc]
  rw [d.hom.naturality v.inv]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc j, hb]
  simp only [Category.assoc]
  rw [← Category.assoc ag, ← hn, hg]
  simp only [Category.assoc]
  have ht := (G.mapIso t).inv_hom_id
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv] at ht
  rw [reassoc_of% ht]
  rw [reassoc_of% hc, reassoc_of% hr]

/-- Finite-stage representative calculation for cancelled normalized reindexing.
Source: Bhatt--Scholze, Remark 6.8.15, explicit inverse-image formula;
composition refinement. First identify the common-stage compositor with finite
integral composition using the localization object transports. Normalize the
integral compositor by the complete-input identifications. Naturality and the
ambient balanced-scalar square then prove coherence of the finite reindexing
isomorphisms. Substitute the three given integral realization formulas and use
naturality to move the transports through them. Cancel the intermediate realization
isomorphism and the mapped comparison for h. The remaining diagram commutes by
finite compositor coherence and naturality of integral realization.
(blueprint: lem-sf-adic-reindexing-functoriality-comp-cancelled-stage)
-/
theorem normalized_reindexing_composition_cancelled_stage
(C : FamilyCore l D)
    (h_moduleComp_sections : ∀ (T U V : GeometricSpace D)
          (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
          (M : modules l V.base.left (C.data V).realization) (W : T.base.left.ProEtᵒᵖ)
          (x : ((modulePull l T.base.left (g ≪≫ h).hom
            (C.ring T V (g ≪≫ h))).obj M).val.obj W),
        HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (h_integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
    (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left) :
    normalized_reindexing_composition_cancelled_equation l D C T U V g h E K := by
  let := (C.data T).units
  let := (C.data U).units
  let := (C.data V).units
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let M := (stageObject l E V.base.left).obj K
  let K' := (constructibleIntegralPullback l A h.hom).obj K
  let F := ordinary l T.base.left (C.data T).realization
  let R := ordinary l U.base.left (C.data U).realization
  let G := derivedPull l T.base.left g.hom (C.ring T U g)
  let H := derivedPull l U.base.left h.hom (C.ring U V h)
  let J := derivedPull l T.base.left (g ≪≫ h).hom (C.ring T V (g ≪≫ h))
  let d : J ≅ H ⋙ G := reindexComp l D C T U V g h
  let e := stagePullIso l h.hom E K
  let p := stagePullIso l g.hom E K'
  let q := stagePullIso l (g ≪≫ h).hom E K
  let c := pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom M
  let k := (pullbackTensorIntegralComposition l A h.hom g.hom).hom.app K
  let b := stageReindexIso l D C T U g E K'
  let bh := stageReindexIso l D C U V h E K
  let bj := stageReindexIso l D C T V (g ≪≫ h) E K
  let r := stageRealizationIso l D C T E
    ((constructibleIntegralPullback l A (g ≪≫ h).hom).obj K)
  let s := stageRealizationIso l D C T E
    ((constructibleIntegralPullback l A g.hom).obj K')
  let t := stageRealizationIso l D C U E K'
  let u := stageRealizationIso l D C V E K
  have hg := stage_normalization l D C T U g E (h_integral_normalization T U g E) K'
  have hh := stage_normalization l D C U V h E (h_integral_normalization U V h E) K
  have hj := stage_normalization l D C T V (g ≪≫ h) E
    (h_integral_normalization T V (g ≪≫ h) E) K
  change (C.comparison T U g).hom.app ((stageObject l E U.base.left).obj K') =
    F.map p.hom ≫ s.hom ≫ b.hom ≫ G.map t.inv at hg
  change (C.comparison U V h).hom.app M =
    R.map e.hom ≫ t.hom ≫ bh.hom ≫ H.map u.inv at hh
  change (C.comparison T V (g ≪≫ h)).hom.app M =
    F.map q.hom ≫ r.hom ≫ bj.hom ≫ J.map u.inv at hj
  have hn := (C.comparison T U g).hom.naturality e.hom
  change F.map ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).map e.hom) ≫
      (C.comparison T U g).hom.app ((stageObject l E U.base.left).obj K') =
    (C.comparison T U g).hom.app
      ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M) ≫
      G.map (R.map e.hom) at hn
  have hc := stagePullIso_composition l g.hom h.hom E K
  change c.hom ≫ (commonStageDerivedPullback l (PadicAlgCl l) g.hom).map e.hom ≫ p.hom =
    q.hom ≫ (stageObject l E T.base.left).map k at hc
  have hr := ((C.data T).realization.integral E).hom.naturality k
  change F.map ((stageObject l E T.base.left).map k) ≫ s.hom =
    r.hom ≫ (pbcDerivedExtend
      (coefficientMap l T.base.left (C.data T).realization E)).map k.hom at hr
  have hb := stageReindexIso_composition l D C T U V g h
    (h_moduleComp_sections T U V g h) E K
  change bj.hom ≫ d.hom.app _ =
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map k.hom ≫
      b.hom ≫ G.map bh.hom at hb
  have hcF := congrArg F.map hc
  simp only [Functor.map_comp] at hcF
  have heq := assembly_square G H J d u t
    (F.map q.hom) r.hom bj.hom
    (F.map c.hom)
    (F.map ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).map e.hom))
    (F.map p.hom) (F.map ((stageObject l E T.base.left).map k)) s.hom
    ((pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map k.hom)
    b.hom bh.hom (R.map e.hom)
    ((C.comparison T V (g ≪≫ h)).hom.app M)
    ((C.comparison T U g).hom.app
      ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M))
    ((C.comparison T U g).hom.app ((stageObject l E U.base.left).obj K'))
    ((C.comparison U V h).hom.app M) hcF hr hb hj hg hh hn
  unfold normalized_reindexing_composition_cancelled_equation
  change (C.comparison T V (g ≪≫ h)).hom.app M ≫ d.hom.app _ ≫
      inv (G.map ((C.comparison U V h).hom.app M)) =
    F.map c.hom ≫ (C.comparison T U g).hom.app
      ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M)
  apply (cancel_mono (G.map ((C.comparison U V h).hom.app M))).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using heq

end WeilConjectures.AdicQbarRealization
