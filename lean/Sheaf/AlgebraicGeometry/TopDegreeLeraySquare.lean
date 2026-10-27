/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.AlgebraicGeometry.GlobalLerayUnitSquare
import Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge

/-! # The top-degree Leray edge on a commutative square

Source: Stacks Project, cohomology.tex, Tags 01E4, 01FB and 08HY.
(blueprint: lem-weil-pbc-top-degree-leray-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

attribute [local instance_reducible] TopCat.Sheaf
set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian Scheme.ringCatSheaf

attribute [local instance 3000] SheafOfModules.instCategory SheafOfModules.instPreadditive
  SheafOfModules.instAbelian

/-- The native category, through the scheme-module alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
local instance (priority := 2000) topDegreeModuleCategory (S : Scheme.{u}) :
    Category S.Modules :=
  SheafOfModules.instCategory (R := moduleRings S.toRingedSpace)

/-- The native additive structure, through the scheme-module alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
local instance (priority := 2000) topDegreeModulePreadditive (S : Scheme.{u}) :
    Preadditive S.Modules :=
  SheafOfModules.instPreadditive (moduleRings S.toRingedSpace)

/-- The native abelian structure, through the scheme-module alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
local instance (priority := 2000) topDegreeModuleAbelian (S : Scheme.{u}) :
    Abelian S.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings S.toRingedSpace)))

set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem nativeModuleAbelian_eq (S : Scheme.{u}) :
    topDegreeModuleAbelian S =
      (inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings S.toRingedSpace)))) := by
  rfl

attribute [local instance 1000] SheafOfModules.instAbelian
attribute [local instance 4000] globalLerayModuleAbelian

/-- The actual cohomology module with scalars restricted to the base scheme.
Source: Stacks, Tag 01F2 and the module-structure remark following Tag 01F4.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeCohomologyOnBase {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    ModuleCat.{u} Γ(S, ⊤) :=
  (ModuleCat.restrictScalars f.appTop.hom).obj
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj F)

attribute [irreducible] topDegreeCohomologyOnBase

/-- The existing cohomology h-map, with both base-module presentations fixed.
Its underlying additive map is independent of the scalar restrictions.
Source: Stacks, Tags 01FB and 0096.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeCohomologyPullback {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (q : Y ⟶ T) (p : Y ⟶ X) (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M) :
    (forget₂ _ AddCommGrpCat.{u}).obj (topDegreeCohomologyOnBase f F) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj (topDegreeCohomologyOnBase q M) := by
  with_unfolding_all
    exact Scheme.Modules.moduleCohomologyFMap p (G := F) (F := M)
      ((Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv F M a) 1

attribute [irreducible] topDegreeCohomologyPullback

/-- The fixed classical edge. Its resolution-cocycle equation determines its value
on every cohomology class, so this selects no arbitrary map.
Source: Stacks, Tags 01F4(2) and 01E4
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeClassicalLerayEdge {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    (RingedSpace.moduleCohomology X.toRingedSpace n ⋙ forget₂ _ AddCommGrpCat) ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived n ⋙
        RingedSpace.globalSectionsFunctor S.toRingedSpace ⋙ forget₂ _ AddCommGrpCat :=
  Classical.choose (exists_lerayEdge_isIso_of_vanishing f) n

attribute [irreducible] topDegreeClassicalLerayEdge

/-- Vanishing makes the specified classical edge invertible.
Source: Stacks, Tag 01F4(2)
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
theorem topDegreeClassicalLerayEdge_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (n : ℕ)
    (hv : ∀ q p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology S.toRingedSpace p).obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F))) :
    IsIso ((topDegreeClassicalLerayEdge f n).app F) := by
  unfold topDegreeClassicalLerayEdge
  exact (Classical.choose_spec (exists_lerayEdge_isIso_of_vanishing f)).2 F hv n

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The actual derived image of a module in degree zero.
Source: Stacks, Tag 01F2.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeDerivedImage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    schemeDerivedCategory.{u, w} S :=
  globalLerayImage.{u, w} f F

/-- The canonical total-to-classical comparison on the specified derived image.
Source: Stacks, Tag 01F2.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeLerayComparison {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1)).obj
        (topDegreeDerivedImage.{u, w} f F) ≅
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F) :=
  globalLerayComparison.{u, w} f F 1

/-- The specified global Leray edge, expressed in total-derived cohomology.
Every class has a cycle representative. The monomorphism from cycles determines the
section in the resolution-cocycle formula, so that formula determines this edge uniquely.
Source: Stacks, Tags 01E4 and 01F4(2).
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeLerayEdge {A B : Scheme.{u}} (k : A ⟶ B) (N : A.Modules) :
    (forget₂ _ AddCommGrpCat.{u}).obj (topDegreeCohomologyOnBase k N) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.globalSectionsFunctor B.toRingedSpace).obj
          (((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings B.toRingedSpace)) 1)).obj
              (topDegreeDerivedImage.{u, w} k N))) := by
  with_unfolding_all
    exact (topDegreeClassicalLerayEdge k 1).app N ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor B.toRingedSpace).map
          (topDegreeLerayComparison.{u, w} k N).inv)

attribute [irreducible] topDegreeLerayEdge

/-- Section pullback along the normalized tensor adjunction at the whole open.
Source: Stacks, Tag 0096.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeSectionPullback {A B : Scheme.{u}} (k : A ⟶ B) (N : B.Modules)
    (z : (RingedSpace.globalSectionsFunctor B.toRingedSpace).obj N) :
    (RingedSpace.globalSectionsFunctor A.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback k).obj N) :=
  ((Scheme.Modules.tensorPullback k).obj N).val.presheaf.map
    (eqToHom (congrArg op (Opens.map_top k.base).symm))
      (((Scheme.Modules.tensorPullbackSectionAdjunction k).unit.app N).app ⊤ z)

attribute [irreducible] topDegreeSectionPullback

/-- The single-module base-change mate, with its derived-image endpoints fixed.
Source: Stacks, Tag 08HY.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeTensorBaseChange
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) :
    (derivedPullback.{u, w} g).obj (topDegreeDerivedImage.{u, w} f F) ⟶
      topDegreeDerivedImage.{u, w} q ((Scheme.Modules.tensorPullback p).obj F) := by
  letI : ∀ {V W : Scheme.{u}} (k : V ⟶ W),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition) k
  with_unfolding_all exact singleDegreeBaseChangeComposite f g p q hs 0 F

attribute [irreducible] topDegreeTensorBaseChange

/-- The derived mate with an arbitrary coefficient morphism, before taking cohomology.
Source: Stacks, Tag 08HY.
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
def topDegreeBaseChangeMap
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M) :
    (derivedPullback.{u, w} g).obj (topDegreeDerivedImage.{u, w} f F) ⟶
      topDegreeDerivedImage.{u, w} q M := by
  with_unfolding_all
    exact topDegreeTensorBaseChange f q g p hs F ≫
      (schemeDerivedDirectImage q).map ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map a)

attribute [irreducible] topDegreeBaseChangeMap

attribute [irreducible] topDegreeDerivedImage topDegreeLerayComparison

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeDerivedImage

attribute [local irreducible] RingedSpace.moduleCohomology
  Scheme.Modules.moduleCohomologyFMap derivedPullbackTopCohomology
  schemeSingleCohomologyComparison derivedSquareUnitMap

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem sectionAdjunction_eq {A B : Scheme.{u}} (k : A ⟶ B) :
    Scheme.Modules.tensorPullbackSectionAdjunction k =
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k) := by
  symm
  apply ((Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction k).choose_spec.2 _)
  intro M U m
  exact (Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction k))
    M (op U) m

section
set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules.pushforward TopCat.instCategorySheaf
  Scheme.Hom.toRingCatSheafHom CochainComplex.singleFunctors HomotopyCategory.singleFunctors
  SingleFunctors.postcomp Functor.mapHomotopyCategory HomotopyCategory.quotient

private theorem singleDirectImage_naturality {A B : Scheme.{u}} (k : A ⟶ B)
    (N P : A.Modules) (b : N ⟶ P) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings B.toRingedSpace)) 0).map
        ((Scheme.Modules.pushforward k).map b) ≫
      Scheme.Modules.canonicalSingleDirectImageMap k P =
    Scheme.Modules.canonicalSingleDirectImageMap k N ≫
      (schemeDerivedDirectImage k).map ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) 0).map b) := by
  let D := RingedSpace.moduleDirectImage k.toLRSHom.toShHom
  let : D.Additive := RingedSpace.moduleDirectImage_additive_proof k.toLRSHom.toShHom
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  have h₁ := (Functor.whiskerRight
    (HomologicalComplex.singleMapHomologicalComplex D (ComplexShape.up ℤ) 0).inv
      Q).naturality b
  have h₂ := D.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.singleFunctor _ 0).map b)
  let σ := (HomologicalComplex.singleMapHomologicalComplex D (ComplexShape.up ℤ) 0).inv
  let S₀ := HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings A.toRingedSpace)) 0
  with_unfolding_all
    change ((D ⋙ HomologicalComplex.single
        (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (ComplexShape.up ℤ) 0) ⋙ Q).map b ≫
        Q.map (σ.app P) ≫ D.rightDerivedFunctorUnit.app (S₀.obj P) =
      (Q.map (σ.app N) ≫ D.rightDerivedFunctorUnit.app (S₀.obj N)) ≫
        (DerivedCategory.Qh ⋙ D.rightDerivedFunctor).map (S₀.map b)
  simp only [Functor.whiskerRight_app] at h₁
  rw [← Category.assoc, h₁, Category.assoc]
  with_unfolding_all erw [h₂]
  simp only [Category.assoc]
  with_unfolding_all rfl

end

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem topDegreeBaseChange_transpose
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M) :
    (@pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} k ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} k)
      _ _ g).homEquiv _ _ (topDegreeBaseChangeMap f q g p hs F M a) =
      globalLerayUnitMap f q g p hs F M
        ((Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv F M a) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  unfold globalLerayUnitMap
  let adj := @pinnedDerivedAdjunction.{u, w} _
    (fun {_ _} k ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} k) _ _ g
  let Sy := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
  have ht := derivedModuleBaseChange_transpose f q g p hs F
  unfold topDegreeBaseChangeMap topDegreeTensorBaseChange
  with_unfolding_all
    change adj.homEquiv _ _
      ((schemeDerivedBaseChangeMap f q g p hs _ ≫
        (schemeDerivedDirectImage q).map (pinnedModulePullbackComparisonAt p 0 F)) ≫
          (schemeDerivedDirectImage q).map (Sy.map a)) = _
  rw [adj.homEquiv_naturality_right, ht, sectionAdjunction_eq]
  unfold derivedSquareUnitMap
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (derivedSquareRightComparison f q g p hs).hom.naturality (Sy.map a)
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  have hm := congrArg (schemeDerivedDirectImage f).map
    (singleDirectImage_naturality p ((Scheme.Modules.tensorPullback p).obj F) M a)
  simp only [Functor.map_comp] at hm
  have hh := congrArg (fun z ↦
    (schemeDerivedDirectImage f).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).unit.app F)) ≫
      z ≫ (derivedSquareRightComparison f q g p hs).hom.app (Sy.obj M)) hm.symm
  simpa only [Category.assoc] using hh

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem topDegreeSection_adjunct {A B : Scheme.{u}} (k : A ⟶ B)
    (N : B.Modules) (P : A.Modules) (b : (Scheme.Modules.tensorPullback k).obj N ⟶ P)
    (z : (RingedSpace.globalSectionsFunctor B.toRingedSpace).obj N) :
    (RingedSpace.globalSectionsFunctor A.toRingedSpace).map b
        (topDegreeSectionPullback k N z) =
      P.val.presheaf.map (eqToHom (congrArg op (Opens.map_top k.base).symm) :
        op (k ⁻¹ᵁ (⊤ : B.Opens)) ⟶ op (⊤ : A.Opens))
        (((Scheme.Modules.tensorPullbackSectionAdjunction k).homEquiv N P b).app ⊤ z) := by
  unfold topDegreeSectionPullback
  rw [Adjunction.homEquiv_unit]
  exact congrArg (fun t ↦ t
    (((Scheme.Modules.tensorPullbackSectionAdjunction k).unit.app N).app ⊤ z))
    (b.val.naturality (eqToHom (congrArg op (Opens.map_top k.base).symm) :
        op (k ⁻¹ᵁ (⊤ : B.Opens)) ⟶ op (⊤ : A.Opens)))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem topDegreeSection_of_adjunct {A B : Scheme.{u}} (k : A ⟶ B)
    (N : B.Modules) (P : A.Modules) (b : (Scheme.Modules.tensorPullback k).obj N ⟶ P)
    (c : N ⟶ (Scheme.Modules.pushforward k).obj P)
    (h : (Scheme.Modules.tensorPullbackSectionAdjunction k).homEquiv _ _ b = c)
    (z : (RingedSpace.globalSectionsFunctor B.toRingedSpace).obj N) :
    (RingedSpace.globalSectionsFunctor A.toRingedSpace).map b
        (topDegreeSectionPullback k N z) =
      P.val.presheaf.map (eqToHom (congrArg op (Opens.map_top k.base).symm) :
        op (k ⁻¹ᵁ (⊤ : B.Opens)) ⟶ op (⊤ : A.Opens)) (Scheme.Modules.Hom.app c ⊤ z) := by
  exact (topDegreeSection_adjunct k N P b z).trans
    (congrArg (fun a : N ⟶ (Scheme.Modules.pushforward k).obj P ↦
      P.val.presheaf.map (eqToHom (congrArg op (Opens.map_top k.base).symm) :
        op (k ⁻¹ᵁ (⊤ : B.Opens)) ⟶ op (⊤ : A.Opens))
          (Scheme.Modules.Hom.app a ⊤ z)) h)

set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeCohomologyOnBase

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem topDegreeCohomologyPullback_apply
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (p : Y ⟶ X)
    (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M)
    (x : topDegreeCohomologyOnBase f F) :
    topDegreeCohomologyPullback f q p F M a x =
      Scheme.Modules.moduleCohomologyFMap p
        ((Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv F M a) 1 x := by
  unfold topDegreeCohomologyPullback
  rfl

private theorem topDegreeLerayEdge_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : topDegreeCohomologyOnBase f F) :
    topDegreeLerayEdge f F x =
      (RingedSpace.globalSectionsFunctor S.toRingedSpace).map
        (globalLerayComparison.{u, w} f F 1).inv
          (((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) 1).app F x) := by
  with_unfolding_all rfl

/-- In top degree one, the adjoint of derived base change acts on global Leray classes
by the specified cohomology pullback. An arbitrary coefficient morphism is allowed;
the square need not be cartesian. No affine, flatness or invertibility assumption on
the base-change map is used.
Source: Stacks Project, cohomology.tex, Tag 01E4, lemma-describe-higher-direct-images;
Tag 01FB, remark-explain-arrow; Tag 08HY, remark-base-change.
(blueprint: lem-weil-pbc-top-degree-leray-square).

Proof:
Transpose the derived base-change mate. Its coefficient comparison is the pinned
single-module counit followed by a[0]. Transport canonicalSingleAdjunctionTranspose
by the unique normalized tensor-to-ordinary pullback isomorphism; its unit equation
identifies the transpose with the ordinary unit followed by a. Write φ for that
ordinary adjunct. If E_(v,k) : Rk_* ∘ Rv_* ≅ R(k∘v)_* denotes the composition
comparison, the derived adjunct of d is Rf_* of the single-module
map F[0] → Rp_*(M[0]) associated to φ, followed by E_(p,f), the equality pf=qg,
and E_(q,g) inverse. Both E maps are characterized by the right-derived-unit equation
in RingedSpace.exists_derivedModuleDirectImageComposition. Their equations identify
this adjunct with the base-change mate, since both transposes are the same unit,
coefficient map and counit.
Apply derivedAdjunction_topEdge in degree one. Its target Rq_*(M[0]) is in D≥0
by Functor.isGE_rightDerivedFunctor_obj_singleFunctor for moduleDirectImage q.
The upper bound on Rf_*(F[0]) makes
its ordinary adjunct the inverse top-cohomology comparison followed by H1 of the
specified derived mate. Its local-class equation identifies the action on classes
with pullback of a resolution cocycle along the ordinary unit and a.
To compute that action, choose an injective resolution of F and of M, resolve p_* of
the latter, and lift the ordinary coefficient morphism. The section quasi-isomorphism
identifies the resulting roof with moduleCohomologyFMap: if I resolves F, J resolves
M, λ : p_*J → L is the injective replacement and β : I → L lifts φ, that map is
H1(Γβ) followed by H1(Γλ) inverse and the canonical whole-open section comparison.
The unit equations for the two E maps represent the derived adjunct by this same
roof after applying f_*. Naturality of local cohomology classes through β and λ
therefore identifies its action with the cocycle class of this cohomology pullback.
Only pf=qg is used, so no cartesian condition is required. At the whole open, the cocycle formula in
exists_lerayEdge_isIso_of_vanishing identifies the local-class maps with its chosen
Leray edges. Transport through the canonical total/classical comparison. Evaluation
of the ordinary adjunction unit at the whole open, followed by restriction along
Opens.map_top, gives exactly the section pullback displayed below. Naturality in a
and functoriality of cohomology finish the formula. No local-class map or derived
base-change map is inverted. Empty schemes and zero coefficients give zero maps. -/
theorem topDegreeLeray_commutativeSquare
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M)
    (hC : (topDegreeDerivedImage.{u, w} f F).IsLE 1) :
    let C := topDegreeDerivedImage.{u, w} f F
    let d := topDegreeBaseChangeMap.{u, w} f q g p hs F M a
    let κ := derivedPullbackTopCohomology g 1 C hC
    letI : IsIso κ := (Classical.choose_spec
      (derivedPullback_topCohomology g 1 C hC)).2.1
    ∀ x : topDegreeCohomologyOnBase f F,
      topDegreeLerayEdge q M (topDegreeCohomologyPullback f q p F M a x) =
      (RingedSpace.globalSectionsFunctor T.toRingedSpace).map
        (inv κ ≫ ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1)).map d)
          (topDegreeSectionPullback g (((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1)).obj C)
              (topDegreeLerayEdge f F x)) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let C := topDegreeDerivedImage.{u, w} f F
  let K := topDegreeDerivedImage.{u, w} q M
  let d := topDegreeBaseChangeMap.{u, w} f q g p hs F M a
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1
  let κ := derivedPullbackTopCohomology g 1 C hC
  have : IsIso κ := (Classical.choose_spec
    (derivedPullback_topCohomology g 1 C hC)).2.1
  have hK : ∃ n : ℤ, K.IsGE n := by
    refine ⟨0, ?_⟩
    exact globalLerayImage_isGE q M
  obtain ⟨e, hE⟩ := (derivedAdjunction_topEdge g 1 C hC K hK).exists
  have he := hE.1
  have ha := congrArg (fun adj : Scheme.Modules.tensorPullback g ⊣
      Scheme.Modules.pushforward g ↦
        adj.homEquiv (HS.obj C) (HT.obj K) (inv κ ≫ HT.map d)) (sectionAdjunction_eq g)
  have hd₀ := ha.trans (hE.2 d)
  have hd := hd₀.trans (congrArg
    (fun z : C ⟶ (schemeDerivedDirectImage g).obj K ↦ HS.map z ≫ e)
    (topDegreeBaseChange_transpose f q g p hs F M a))
  intro x
  have hg := globalLeray_unitSquare f q g p hs F M
    ((Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv F M a) 1 e he x
  have hq := (topDegreeLerayEdge_apply q M
    (topDegreeCohomologyPullback f q p F M a x)).trans
      (congrArg (fun z ↦ (RingedSpace.globalSectionsFunctor T.toRingedSpace).map
        (globalLerayComparison.{u, w} q M 1).inv
          (((Classical.choose (exists_lerayEdge_isIso_of_vanishing q)) 1).app M z))
        (topDegreeCohomologyPullback_apply f q p F M a x))
  have hf := congrArg (fun z ↦ (HT.obj K).val.presheaf.map
    (eqToHom (congrArg op (Opens.map_top g.base).symm) :
      op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens))
      (Scheme.Modules.Hom.app (HS.map (globalLerayUnitMap f q g p hs F M
        ((Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv F M a)) ≫ e) ⊤ z))
    (topDegreeLerayEdge_apply f F x)
  have hg' := hq.trans (hg.trans hf.symm)
  have hx := topDegreeSection_of_adjunct g (HS.obj C) (HT.obj K)
    (inv κ ≫ HT.map d) _ hd (topDegreeLerayEdge f F x)
  exact hg'.trans hx.symm

end AlgebraicGeometry
