/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.ExactProductsRoosComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Normalized direct image of canonical Roos triangles

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0941; Derived Categories,
Tag 0BK6, with the explicit strict cone normalization in the DAG
(blueprint: lem-weil-pbc-direct-image-roos-normalization).

The structures below only package the choices of total derived functors, units and
canonical comparisons already appearing in the statement. The conclusion constructs
Roos triangles with normalization on every complex, rather than choosing cone vertices
up to an unspecified isomorphism. The index `n : ℕ` denotes positive level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uA vA uB vB g

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory
namespace DirectImageRoosNormalization

section PrivateElementary

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

private theorem nat_products
    {E : Type*} [Category E] [HasCountableProducts E] :
    HasLimitsOfShape (Discrete ℕ) E := HasCountableProducts.out ℕ

private theorem cochain_nat_products
    {E : Type*} [Category E] [Abelian E] [HasCountableProducts E] :
    HasLimitsOfShape (Discrete ℕ) (CochainComplex E ℤ) := inferInstance

private theorem paste_boundary
    {E : Type*} [Category E] {P R S T V W F H : E}
    {a : P ⟶ R} {b : R ⟶ S} {c : S ⟶ T} {d : P ⟶ V} {e : V ⟶ W}
    {t : W ⟶ T} {k : T ⟶ H} {l : W ⟶ F} {m : F ⟶ H}
    (hu : a ≫ b ≫ c = d ≫ e ≫ t) (hn : t ≫ k = l ≫ m) :
    d ≫ e ≫ l ≫ m = (a ≫ b) ≫ c ≫ k := by
  rw [← hn]
  simpa only [Category.assoc] using (congrArg (fun f ↦ f ≫ k) hu).symm

private theorem comp_biprod_lift
    {A₀ : Type*} [Category A₀] [Abelian A₀] {W X Y Z : A₀}
    (h : W ⟶ X) (a : X ⟶ Y) (b : X ⟶ Z) :
    h ≫ biprod.lift a b = biprod.lift (h ≫ a) (h ≫ b) := by
  apply biprod.hom_ext <;> simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]

private theorem map_biprod_lift
    {A₀ B₀ : Type*} [Category A₀] [Abelian A₀] [Category B₀] [Abelian B₀]
    (G : A₀ ⥤ B₀) [G.Additive] {W X Y : A₀} {X' Y' : B₀}
    (a : W ⟶ X) (b : W ⟶ Y) (f : G.obj X ⟶ X') (g : G.obj Y ⟶ Y') :
    G.map (biprod.lift a b) ≫ G.biprodComparison X Y ≫ biprod.map f g =
      biprod.lift (G.map a ≫ f) (G.map b ≫ g) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
      Functor.biprodComparison_fst_assoc, Functor.biprodComparison_snd_assoc,
      ← G.map_comp_assoc, biprod.lift_fst, biprod.lift_snd]

end PrivateElementary

variable (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- Total derived inverse limit and evaluation of strict towers, with their units.
Source: Stacks Tags 0940 and 0941
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
This packages the interface of `ringedStrictTowerHomotopyLimitIndependentCoefficients`.
It introduces no new inverse-limit or evaluation construction. -/
structure LimitData where
  limit : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A
  unit : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ limit
  derived : limit.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  unit_isIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (unit.app I)
  evaluation : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A)
  evaluationIso : DerivedCategory.Q ⋙ evaluation ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
        (DerivedCategory.{w} A)).obj DerivedCategory.Q

variable {A}
variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- The normalized derived direct-image comparison of strict inverse limits.
Source: Stacks Tag 0A07 and the common-underived-composite normalization
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
The fields are precisely choices in `ringedTowerPushforwardLimitComparison`.
`ordinary_components` fixes the underived comparison; `comparison_unit` fixes `a`.
The evaluation comparison is fixed on K-injectives, including all transitions. -/
structure DirectImageData (G : A ⥤ B) [G.Additive] where
  source : LimitData.{w} A
  target : LimitData.{w} B
  direct : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B
  tower : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B)
  unit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ direct
  towerUnit : ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ tower
  direct_derived : direct.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso A (.up ℤ))
  tower_derived : tower.IsRightDerivedFunctor towerUnit
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  unit_isIso : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)
  towerUnit_isIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → IsIso (towerUnit.app I)
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ G ≅
    (Functor.whiskeringRight ℕᵒᵖ A B).obj G ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  ordinary_components : ∀ (H : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ),
    ordinary.hom.app H ≫ limit.π (H ⋙ G) n = G.map (limit.π H n)
  comparison : source.limit ⋙ direct ≅ tower ⋙ target.limit
  comparison_unit : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    unit.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        direct.map (source.unit.app X) ≫ comparison.hom.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.unit.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.limit.map (towerUnit.app X)
  evaluationIso : tower ⋙ target.evaluation ≅ source.evaluation ⋙
    (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory.{w} A) (DerivedCategory.{w} B)).obj direct
  evaluation_unit : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective → ∀ n : ℕᵒᵖ,
    (target.evaluation.map (towerUnit.app I)).app n ≫
        (evaluationIso.hom.app (DerivedCategory.Q.obj I)).app n ≫
        direct.map ((source.evaluationIso.hom.app I).app n) =
      (target.evaluationIso.hom.app
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        unit.app (I.asFunctor.obj n)

variable [HasCountableProducts A] [HasCountableProducts (DerivedCategory.{w} A)]

/-- The ordinary-limit inclusion into the existing strict Roos cone, with coordinates
`(0, (λ_n)_n)`. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
The domain is termwise ordinary limit, as in the total-derived-functor unit. -/
def ordinaryInclusion (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (ExactProductsRoos.ordinary (B := A)).obj X ⟶ roosF.obj X :=
  roosLift (ExactProductsRoos.inclusion.app X) (ExactProductsRoos.inclusion_difference X)

section PrivateComparisons

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

attribute [local instance 1050] nat_products
attribute [local instance 1100] cochain_nat_products

set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts A]
  [HasCountableProducts (DerivedCategory A)] in
private theorem coneArrowMap_eq
    {X Y X' Y' : CochainComplex A ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (α : Arrow.mk f ⟶ Arrow.mk g) : HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α =
      CochainComplex.mappingCone.map f g α.left α.right α.w.symm := by
  ext n : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f,
      Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero,
      ]
    change _ = (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _ (n + 1) (n + 1) n (by omega) (by omega)]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v]
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_desc_f]
    change _ = (CochainComplex.mappingCone.inr f).f n ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl


@[irreducible]
private def roosSignComponent (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ExactProductsRoos.fibre.obj X ≅ roosF.obj X :=
  (shiftFunctor _ (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso _ _
      (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.isoMk (Iso.refl _) (-(Iso.refl _)) (by simp)))

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasCountableProducts (DerivedCategory A)] in
private theorem roosF_map_arrow {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : X ⟶ Y) :
    roosF.map f =
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
        (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
        (Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm))⟦(-1 : ℤ)⟧' := by
  rw [coneArrowMap_eq]
  rfl

private def roosSign :
    Iso (C := CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
      ExactProductsRoos.fibre roosF :=
  NatIso.ofComponents (fun X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ↦ roosSignComponent X) (by
    intro X Y f
    let H : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j :=
      fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩
    let a (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        Arrow.mk (-roosU Z) ≅ Arrow.mk (roosU Z) :=
      Arrow.isoMk (Iso.refl _) (-(Iso.refl _)) (by simp)
    let β : Arrow.mk (roosU X) ⟶ Arrow.mk (roosU Y) :=
      Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm
    have h : ExactProductsRoos.arrowMap f ≫ (a Y).hom = (a X).hom ≫ β := by
      apply Arrow.hom_ext <;> simp [a, β, ExactProductsRoos.arrowMap,
        Arrow.isoMk, roosPmap, ExactProductsRoos.product]
    rw [roosF_map_arrow]
    unfold roosSignComponent
    change (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H
          (ExactProductsRoos.arrowMap f)) ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H (a Y).hom) =
      (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H (a X).hom) ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H β)
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
    exact (HomologicalComplex.homotopyCofiber.mapArrowHom_comp
      (-roosU X) (-roosU Y) (roosU Y) H (ExactProductsRoos.arrowMap f) (a Y).hom).symm.trans
      ((congrArg (HomologicalComplex.homotopyCofiber.mapArrowHom
        (-roosU X) (roosU Y) H) h).trans
        (HomologicalComplex.homotopyCofiber.mapArrowHom_comp
          (-roosU X) (roosU X) (roosU Y) H (a X).hom β)))

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasCountableProducts (DerivedCategory A)] in
private theorem ordinaryInclusion_f (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ordinaryInclusion X).f p = (ExactProductsRoos.inclusion.app X).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (roosU X) p (p + (-1))
        (by change p + (-1) + 1 = p; omega) := by
  simp only [ordinaryInclusion, roosLift, CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ p _ _ (p + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory
  A)] in
private theorem roosSign_inclusion (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ExactProductsRoos.comparison.app X ≫ roosSign.hom.app X = ordinaryInclusion X := by
  ext p : 1
  change (ExactProductsRoos.comparisonApp X).f p ≫
    (roosSignComponent X).hom.f p = _
  rw [ExactProductsRoos.comparisonApp_f, ordinaryInclusion_f]
  simp only [roosSignComponent, Functor.mapIso_hom,
    HomologicalComplex.homotopyCofiber.mapArrowIso_hom]
  rw [CochainComplex.shiftFunctor_map_f']
  rw [Category.assoc]
  dsimp only [HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  · simp
  · change p + -1 + 1 = p
    omega

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory
  A)] in
private theorem ordinaryInclusion_χ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ordinaryInclusion X).f (p + 1) ≫ (roosχ X p).hom =
      biprod.lift 0 ((ExactProductsRoos.inclusion.app X).f (p + 1)) :=
  roosLift_χ _ _ p


omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory
  A)] in
private theorem ordinaryInclusion_projection (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ordinaryInclusion X ≫ roosProj X = ExactProductsRoos.inclusion.app X := by
  apply HomologicalComplex.hom_ext
  intro k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (ordinaryInclusion X ≫ roosProj X).f (p + 1) =
    (ExactProductsRoos.inclusion.app X).f (p + 1)
  simp only [HomologicalComplex.comp_f, roosProj_f, ← Category.assoc,
    ordinaryInclusion_χ, biprod.lift_snd]

private def roosProjection : roosF ⟶ ExactProductsRoos.product (B := A) where
  app X := roosProj X
  naturality X Y f := by
    change roosF.map f ≫ roosProj Y = roosProj X ≫ roosPmap f
    apply Pi.hom_ext
    intro n
    simpa only [roosEval, roosPmap, Category.assoc, Pi.map_π] using
      roosEval_natural f n

private def roosBoundary :
    ExactProductsRoos.product (B := A) ⟶ roosF ⋙ shiftFunctor _ (1 : ℤ) where
  app X := (CochainComplex.mappingCocone.triangle (roosU X)).mor₃
  naturality X Y f := by
    dsimp only [CochainComplex.mappingCocone.triangle,
      CochainComplex.mappingCone.triangle, Triangle.mk, Functor.comp_map]
    simp only [Category.assoc]
    let e := shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by omega)
    change roosPmap f ≫ CochainComplex.mappingCone.inr (roosU Y) ≫
        e.inv.app (CochainComplex.mappingCone (roosU Y)) =
      CochainComplex.mappingCone.inr (roosU X) ≫
        e.inv.app (CochainComplex.mappingCone (roosU X)) ≫
        (roosF.map f)⟦(1 : ℤ)⟧'
    rw [← Category.assoc,
      show roosPmap f ≫ CochainComplex.mappingCone.inr (roosU Y) =
        CochainComplex.mappingCone.inr (roosU X) ≫ roosConeFunctor.map f from
          (CochainComplex.mappingCone.triangleMap (roosU X) (roosU Y)
            (roosPmap f) (roosPmap f) (roosU_natural f)).comm₂.symm, Category.assoc]
    congr 1
    exact e.inv.naturality (roosConeFunctor.map f)

private def roosBoundaryQ :
    ExactProductsRoos.product (B := A) ⋙ DerivedCategory.Q ⟶
      (roosF ⋙ DerivedCategory.Q) ⋙ shiftFunctor _ (1 : ℤ) :=
  Functor.whiskerRight roosBoundary DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft roosF (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom ≫
    (Functor.associator _ _ _).inv

set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory A)] in
private theorem roosBoundary_f_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosBoundary.app X).f p ≫ (roosχ X p).hom = biprod.lift (𝟙 _) 0 := by
  apply biprod.hom_ext <;>
    simp [roosBoundary, CochainComplex.mappingCocone.triangle,
      CochainComplex.mappingCone.triangle, roosχ, roosF, roosConeFunctor,
      shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_hom_app_f',
      CochainComplex.shiftFunctorZero_inv_app_f,
      CochainComplex.mappingCone.inr,
      HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]

set_option backward.defeqAttrib.useBackward true in
omit [HasCountableProducts (DerivedCategory A)] in
private theorem normalizedConeComparison
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    [HasExactLimitsOfShape (Discrete ℕ) A] (L : LimitData.{w} A) :
    ∃ e : roosF (A := A) ⋙ DerivedCategory.Q ≅
      (DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)) ⋙ L.limit,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        DerivedCategory.Q.map (ordinaryInclusion X) ≫ e.hom.app X = L.unit.app X := by
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso L.limit L.unit L.unit_isIso
  refine ⟨Functor.isoWhiskerRight roosSign.symm DerivedCategory.Q ≪≫ e, ?_⟩
  intro X
  have hs : ordinaryInclusion X ≫ roosSign.inv.app X =
      ExactProductsRoos.comparison.app X := by
    rw [← roosSign_inclusion X]
    simp
  change DerivedCategory.Q.map (ordinaryInclusion X) ≫
      DerivedCategory.Q.map (roosSign.inv.app X) ≫ e.hom.app X = _
  rw [← DerivedCategory.Q.map_comp_assoc, hs]
  exact congr_app he X

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem productComparison_isIso
    [HasExactLimitsOfShape (Discrete ℕ) A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsIso (piComparison DerivedCategory.Q (fun n : ℕ ↦ X.asFunctor.obj (op n))) := by
  let : CountableAB4Star A := CountableAB4Star.of_hasExactLimitsOfShape_nat A
  obtain ⟨_, hp, _⟩ := derivedCategory_countableProducts_core.{0} A
  let K := fun n : ℕ ↦ X.asFunctor.obj (op n)
  have hf : IsLimit (Fan.mk (DerivedCategory.Q.obj (roosP X))
      (fun n : ℕ ↦ DerivedCategory.Q.map (Pi.π K n))) :=
    (Fan.isLimitMapConeEquiv DerivedCategory.Q K (limit.cone _)) (hp ℕ K).some
  have he : piComparison DerivedCategory.Q K =
      (IsLimit.conePointUniqueUpToIso hf (productIsProduct _)).hom := by
    apply Pi.hom_ext
    intro n
    exact (piComparison_comp_π _ _ n).trans
      (IsLimit.conePointUniqueUpToIso_hom_comp hf (productIsProduct _) ⟨n⟩).symm
  rw [he]
  infer_instance

@[irreducible]
private def normalizedProductComparison [HasExactLimitsOfShape (Discrete ℕ) A]
    (L : LimitData.{w} A) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj (roosP X) ≅
      ∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj (DerivedCategory.Q.obj X)).obj (op n)) :=
  letI := productComparison_isIso X
  asIso (piComparison DerivedCategory.Q (fun n : ℕ ↦ X.asFunctor.obj (op n))) ≪≫
    Pi.mapIso (fun n : ℕ ↦ (L.evaluationIso.app X).symm.app (op n))

@[reassoc]
private theorem normalizedProductComparison_π
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (L : LimitData.{w} A) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (normalizedProductComparison L X).hom ≫ Pi.π _ n =
      DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n) ≫
        (L.evaluationIso.inv.app X).app (op n) := by
  simp only [normalizedProductComparison, Iso.trans_hom, asIso_hom,
    Category.assoc, Pi.mapIso_hom_π, piComparison_comp_π_assoc, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv]

private def derivedProducts :
    (ℕᵒᵖ ⥤ DerivedCategory.{w} A) ⥤ DerivedCategory.{w} A where
  obj M := ∏ᶜ (fun n : ℕ ↦ M.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
  map_id M := by
    apply Pi.hom_ext
    intro n
    simp
  map_comp f k := by simp [Limits.Pi.map_comp_map]

private def normalizedProductIso [HasExactLimitsOfShape (Discrete ℕ) A]
    (L : LimitData.{w} A) :
    ExactProductsRoos.product ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ L.evaluation ⋙ derivedProducts :=
  NatIso.ofComponents (normalizedProductComparison L) (by
    intro X Y f
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc]
    change DerivedCategory.Q.map (roosPmap f) ≫
        (normalizedProductComparison L Y).hom ≫ Pi.π _ n =
      (normalizedProductComparison L X).hom ≫
        Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.map (DerivedCategory.Q.map f)).app (op n)) ≫
          Pi.π _ n
    simp only [normalizedProductComparison_π,
      normalizedProductComparison_π_assoc, Pi.map_π]
    rw [← DerivedCategory.Q.map_comp_assoc, Pi.map_π,
      DerivedCategory.Q.map_comp, Category.assoc]
    congr 1
    exact congr_app (L.evaluationIso.inv.naturality f) (op n))

private theorem normalizedProductComparison_difference
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (L : LimitData.{w} A) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.map (roosU X) ≫ (normalizedProductComparison L X).hom =
      (normalizedProductComparison L X).hom ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ (L.evaluation.obj (DerivedCategory.Q.obj X)).map
          (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.id_comp, Category.assoc, Pi.lift_π,
    normalizedProductComparison_π]
  rw [← DerivedCategory.Q.map_comp_assoc]
  simp only [
    Preadditive.sub_comp, Category.id_comp, Pi.lift_π, Functor.map_sub,
    Functor.map_comp, Preadditive.sub_comp, Category.assoc]
  congr 1
  rw [normalizedProductComparison_π_assoc]
  congr 1
  exact (L.evaluationIso.inv.app X).naturality (homOfLE (Nat.le_succ n)).op

end PrivateComparisons

/-- The canonical Roos triangle, specified on every representing complex.
Source: Stacks Tags 0941 and 0A07, with the DAG's explicit cone convention
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
`normalization` characterizes the comparison with total derived limit by its unit.
It is equivalently the exact-products fibre comparison followed by `(y,x) ↦ (-y,x)`:
both carry the ordinary-limit inclusion to that unit. The last two fields transport
exactly the first and connecting arrows of the rotated strict cone triangle. -/
structure RoosTriangleData (L : LimitData.{w} A) where
  projection : ∀ M, L.limit.obj M ⟶ ∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj M).obj (op n))
  boundary : ∀ M, (∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj M).obj (op n))) ⟶
    (L.limit.obj M)⟦(1 : ℤ)⟧
  distinguished : ∀ M, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (L.evaluation.obj M).map (homOfLE (Nat.le_succ n)).op)
    (L.limit.obj M) (projection M) (boundary M)
  projection_natural : ∀ {M N} (f : M ⟶ N),
    L.limit.map f ≫ projection N = projection M ≫
      Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.map f).app (op n))
  boundary_natural : ∀ {M N} (f : M ⟶ N),
    Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.map f).app (op n)) ≫ boundary N =
      boundary M ≫ (L.limit.map f)⟦(1 : ℤ)⟧'
  coneComparison : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.limit
  normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.map (ordinaryInclusion X) ≫ coneComparison.hom.app X = L.unit.app X
  productComparison : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.obj (roosP X) ≅
      ∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj (DerivedCategory.Q.obj X)).obj (op n))
  product_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    (productComparison X).hom ≫ Pi.π _ n =
      DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n) ≫
        (L.evaluationIso.inv.app X).app (op n)
  projection_model : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    coneComparison.hom.app X ≫ projection (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (roosProj X) ≫ (productComparison X).hom
  boundary_model : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (productComparison X).hom ≫ boundary (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU X)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
        (coneComparison.hom.app X)⟦(1 : ℤ)⟧'

section PrivateTriangles

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

attribute [local instance 1050] nat_products
attribute [local instance 1100] cochain_nat_products

private def derivedDifference : derivedProducts (A := A) ⟶ derivedProducts where
  app M := towerTransitionEndomorphism
    (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)
  naturality M N f := by
    dsimp only [derivedProducts]
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact (f.naturality (homOfLE (Nat.le_succ n)).op).symm

private theorem normalizedRoosTriangle
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    [HasExactLimitsOfShape (Discrete ℕ) A] (L : LimitData.{w} A) :
    Nonempty (RoosTriangleData L) := by
  obtain ⟨e, he⟩ := normalizedConeComparison L
  let θ := normalizedProductIso L
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  let ppre : DerivedCategory.Q ⋙ L.limit ⟶
      DerivedCategory.Q ⋙ L.evaluation ⋙ derivedProducts :=
    e.inv ≫ Functor.whiskerRight roosProjection DerivedCategory.Q ≫ θ.hom
  let bpre : DerivedCategory.Q ⋙ L.evaluation ⋙ derivedProducts ⟶
      DerivedCategory.Q ⋙ L.limit ⋙ shiftFunctor _ (1 : ℤ) :=
    θ.inv ≫ roosBoundaryQ ≫ Functor.whiskerRight e.hom (shiftFunctor _ (1 : ℤ))
  let p := Localization.liftNatTrans DerivedCategory.Q W _ _ L.limit
    (L.evaluation ⋙ derivedProducts) ppre
  let b := Localization.liftNatTrans DerivedCategory.Q W _ _
    (L.evaluation ⋙ derivedProducts) (L.limit ⋙ shiftFunctor _ (1 : ℤ)) bpre
  have hp (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      p.app (DerivedCategory.Q.obj X) = e.inv.app X ≫
        DerivedCategory.Q.map (roosProj X) ≫ (normalizedProductComparison L X).hom := by
    simp [p, ppre, θ, normalizedProductIso, roosProjection, Localization.liftNatTrans_app]
  have hb (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      b.app (DerivedCategory.Q.obj X) = (normalizedProductComparison L X).inv ≫
        DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU X)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
            (e.hom.app X)⟦(1 : ℤ)⟧' := by
    simp [b, bpre, θ, normalizedProductIso, roosBoundaryQ, roosBoundary,
      Localization.liftNatTrans_app]
  have hQ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (L.evaluation.obj (DerivedCategory.Q.obj X)).map
        (homOfLE (Nat.le_succ n)).op)
      (L.limit.obj (DerivedCategory.Q.obj X))
      (p.app (DerivedCategory.Q.obj X)) (b.app (DerivedCategory.Q.obj X)) := by
    let T := DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCocone.triangle (roosU X))
    let U := Triangle.mk (p.app (DerivedCategory.Q.obj X))
      (derivedDifference.app (L.evaluation.obj (DerivedCategory.Q.obj X)))
      (b.app (DerivedCategory.Q.obj X))
    have ei : T ≅ U := by
      refine Triangle.isoMk _ _ (e.app X) (normalizedProductComparison L X)
        (normalizedProductComparison L X) ?_ ?_ ?_
      · change DerivedCategory.Q.map (roosProj X) ≫ _ =
          e.hom.app X ≫ p.app (DerivedCategory.Q.obj X)
        rw [hp]
        simp
      · exact normalizedProductComparison_difference L X
      · change (DerivedCategory.Q.map
            (CochainComplex.mappingCocone.triangle (roosU X)).mor₃ ≫
              (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X)) ≫
                (e.hom.app X)⟦(1 : ℤ)⟧' =
          (normalizedProductComparison L X).hom ≫ b.app (DerivedCategory.Q.obj X)
        rw [hb]
        simp
    exact Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.mappingCocone_triangle_distinguished (roosU X)) _ ei.symm
  refine ⟨⟨p.app, b.app, ?_, fun f ↦ p.naturality f, fun f ↦ b.naturality f,
    e, he, normalizedProductComparison L, normalizedProductComparison_π L, ?_, ?_⟩⟩
  · intro M
    let X := DerivedCategory.Q.objPreimage M
    let a := DerivedCategory.Q.objObjPreimageIso M
    let T := Triangle.mk (p.app (DerivedCategory.Q.obj X))
      (derivedDifference.app (L.evaluation.obj (DerivedCategory.Q.obj X)))
      (b.app (DerivedCategory.Q.obj X))
    let U := Triangle.mk (p.app M) (derivedDifference.app (L.evaluation.obj M)) (b.app M)
    let ei : T ≅ U := Triangle.isoMk _ _ (L.limit.mapIso a)
      ((L.evaluation ⋙ derivedProducts).mapIso a)
      ((L.evaluation ⋙ derivedProducts).mapIso a)
      (p.naturality a.hom).symm
      (derivedDifference.naturality (L.evaluation.map a.hom)).symm
      (b.naturality a.hom).symm
    exact Pretriangulated.isomorphic_distinguished _ (hQ X) _ ei.symm
  · intro X
    rw [hp]
    simp
  · intro X
    rw [hb]
    simp

private theorem projection_unit (L : LimitData.{w} A) (T : RoosTriangleData L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    L.unit.app X ≫ T.projection (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (ExactProductsRoos.inclusion.app X) ≫
        (T.productComparison X).hom := by
  rw [← T.normalization X, Category.assoc, T.projection_model,
    ← DerivedCategory.Q.map_comp_assoc, ordinaryInclusion_projection]

private theorem ordinaryInclusion_Q_isIso (L : LimitData.{w} A)
    (T : RoosTriangleData L) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    IsIso (DerivedCategory.Q.map (ordinaryInclusion I)) := by
  let := L.unit_isIso I inferInstance
  have h : IsIso (DerivedCategory.Q.map (ordinaryInclusion I) ≫
      T.coneComparison.hom.app I) := by
    rw [T.normalization I]
    infer_instance
  exact IsIso.of_isIso_comp_right (DerivedCategory.Q.map (ordinaryInclusion I))
    (T.coneComparison.hom.app I)

private def projectionNat {L : LimitData.{w} A} (T : RoosTriangleData L) :
    L.limit ⟶ L.evaluation ⋙ derivedProducts where
  app := T.projection
  naturality _ _ f := T.projection_natural f

private def boundaryNat {L : LimitData.{w} A} (T : RoosTriangleData L) :
    L.evaluation ⋙ derivedProducts ⟶ L.limit ⋙ shiftFunctor _ (1 : ℤ) where
  app := T.boundary
  naturality _ _ f := T.boundary_natural f

end PrivateTriangles

variable [HasCountableProducts (DerivedCategory.{w} B)]

/-- The product comparison whose components are the images of product projections.
Source: Stacks Tag 0A07 (blueprint: lem-weil-pbc-direct-image-roos-normalization). -/
def alpha {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :=
  piComparison d.direct (fun n : ℕ ↦ (d.source.evaluation.obj M).obj (op n))

/-- The same product comparison with its target identified by derived strict evaluation.
Source: Stacks Tag 0A07 (blueprint: lem-weil-pbc-direct-image-roos-normalization). -/
def productMap {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.obj (∏ᶜ (fun n : ℕ ↦ (d.source.evaluation.obj M).obj (op n))) ⟶
      ∏ᶜ (fun n : ℕ ↦ (d.target.evaluation.obj (d.tower.obj M)).obj (op n)) :=
  alpha d M ≫ Limits.Pi.map (fun n : ℕ ↦ (d.evaluationIso.inv.app M).app (op n))

variable [HasCountableProducts B]

section PrivateSquares

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

attribute [local instance 1050] nat_products
attribute [local instance 1100] cochain_nat_products

omit [HasCountableProducts A] [HasCountableProducts B] in
@[reassoc]
private theorem productMap_π {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (n : ℕ) :
    productMap d M ≫ Pi.π _ n =
      d.direct.map (Pi.π _ n) ≫ (d.evaluationIso.inv.app M).app (op n) := by
  simp only [productMap, alpha, Category.assoc, Pi.map_π, piComparison_comp_π_assoc]

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)]
  [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
@[reassoc]
private theorem unit_naturality {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ d.unit.app Y =
      d.unit.app X ≫ d.direct.map (DerivedCategory.Q.map f) :=
  d.unit.naturality f

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
private theorem evaluation_unit_inv {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (n : ℕᵒᵖ) :
    d.unit.app (I.asFunctor.obj n) ≫
        d.direct.map ((d.source.evaluationIso.inv.app I).app n) ≫
        (d.evaluationIso.inv.app (DerivedCategory.Q.obj I)).app n =
      (d.target.evaluationIso.inv.app
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        (d.target.evaluation.map (d.towerUnit.app I)).app n := by
  let J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  let eS : (d.source.evaluation.obj (DerivedCategory.Q.obj I)).obj n ≅
      DerivedCategory.Q.obj (I.asFunctor.obj n) := (d.source.evaluationIso.app I).app n
  let eT : (d.target.evaluation.obj (DerivedCategory.Q.obj J)).obj n ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        (I.asFunctor.obj n)) := (d.target.evaluationIso.app J).app n
  let e : (d.target.evaluation.obj (d.tower.obj (DerivedCategory.Q.obj I))).obj n ≅
      d.direct.obj ((d.source.evaluation.obj (DerivedCategory.Q.obj I)).obj n) :=
    (d.evaluationIso.app (DerivedCategory.Q.obj I)).app n
  let τ : (d.target.evaluation.obj (DerivedCategory.Q.obj J)).obj n ⟶
      (d.target.evaluation.obj (d.tower.obj (DerivedCategory.Q.obj I))).obj n :=
    (d.target.evaluation.map (d.towerUnit.app I)).app n
  let η : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
      (I.asFunctor.obj n)) ⟶ d.direct.obj (DerivedCategory.Q.obj (I.asFunctor.obj n)) :=
    d.unit.app (I.asFunctor.obj n)
  have h : τ ≫ e.hom ≫ d.direct.map eS.hom = eT.hom ≫ η :=
    d.evaluation_unit I inferInstance n
  change η ≫ d.direct.map eS.inv ≫ e.inv = eT.inv ≫ τ
  calc
    _ = eT.inv ≫ (eT.hom ≫ η) ≫ d.direct.map eS.inv ≫ e.inv := by
      simp only [Category.assoc, eT.inv_hom_id_assoc]
    _ = eT.inv ≫ (τ ≫ e.hom ≫ d.direct.map eS.hom) ≫
        d.direct.map eS.inv ≫ e.inv := by rw [h]
    _ = _ := by
      simp only [Category.assoc, ← d.direct.map_comp_assoc, eS.hom_inv_id,
        Functor.map_id, Category.id_comp, e.hom_inv_id, Category.comp_id]


private theorem productMap_unit {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    d.unit.app (roosP I) ≫ d.direct.map (T.productComparison I).hom ≫
        productMap d (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (piComparison (G.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ I.asFunctor.obj (op n))) ≫
        (U.productComparison
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          Limits.Pi.map (fun n : ℕ ↦
            (d.target.evaluation.map (d.towerUnit.app I)).app (op n)) := by
  let J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  have hπ (n : ℕ) :
      Limits.Pi.map (fun k : ℕ ↦
          (d.target.evaluation.map (d.towerUnit.app I)).app (op k)) ≫
        Pi.π (fun k : ℕ ↦
          (d.target.evaluation.obj (d.tower.obj (DerivedCategory.Q.obj I))).obj (op k)) n =
      Pi.π (fun k : ℕ ↦
          (d.target.evaluation.obj (DerivedCategory.Q.obj J)).obj (op k)) n ≫
        (d.target.evaluation.map (d.towerUnit.app I)).app (op n) :=
    Pi.map_π _ n
  have hc (n : ℕ) :
      piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun k : ℕ ↦ I.asFunctor.obj (op k)) ≫
        Pi.π (fun k : ℕ ↦ J.asFunctor.obj (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n) :=
    piComparison_comp_π _ _ n
  dsimp only [J] at hπ hc
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productMap_π, hπ]
  rw [← d.direct.map_comp_assoc, T.product_components, d.direct.map_comp]
  simp only [Category.assoc]
  rw [← unit_naturality_assoc d (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n),
    evaluation_unit_inv]
  rw [reassoc_of% U.product_components, ← DerivedCategory.Q.map_comp_assoc, hc]

set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts (DerivedCategory A)] [HasCountableProducts (DerivedCategory B)] in
private theorem ordinary_product_square {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (ExactProductsRoos.inclusion.app I) ≫
        piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ I.asFunctor.obj (op n)) =
      (NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I ≫
        ExactProductsRoos.inclusion.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I) := by
  apply Pi.hom_ext (f := fun n : ℕ ↦
    (HomologicalComplex.asFunctor
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).obj (op n))
  intro n
  have h : piComparison (G.mapHomologicalComplex (.up ℤ))
        (fun k : ℕ ↦ I.asFunctor.obj (op k)) ≫
      Pi.π (fun k : ℕ ↦
        (HomologicalComplex.asFunctor
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).obj
          (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n) :=
    piComparison_comp_π _ _ n
  rw [Category.assoc, h, ← Functor.map_comp]
  simp only [Category.assoc, Pi.lift_π]
  ext p
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  exact (d.ordinary_components (I.X p) (op n)).symm


set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_square_on_KInjective {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    d.direct.map (T.projection (DerivedCategory.Q.obj I)) ≫
        productMap d (DerivedCategory.Q.obj I) =
      d.comparison.hom.app (DerivedCategory.Q.obj I) ≫
        U.projection (d.tower.obj (DerivedCategory.Q.obj I)) := by
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let := d.source.unit_isIso I inferInstance
  let := d.unit_isIso (ExactProductsRoos.ordinary.obj I) inferInstance
  apply (cancel_epi (d.unit.app (ExactProductsRoos.ordinary.obj I) ≫
    d.direct.map (d.source.unit.app I))).mp
  let J := (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  calc
    _ = DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map (ExactProductsRoos.inclusion.app I)) ≫
          d.unit.app (roosP I) ≫ d.direct.map (T.productComparison I).hom ≫
            productMap d (DerivedCategory.Q.obj I) := by
      simp only [Category.assoc]
      rw [← d.direct.map_comp_assoc,
        projection_unit, d.direct.map_comp]
      simp only [Category.assoc]
      rw [← unit_naturality_assoc d]
    _ = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫
          DerivedCategory.Q.map (ExactProductsRoos.inclusion.app J) ≫
            (U.productComparison J).hom ≫
              Limits.Pi.map (fun n : ℕ ↦
                (d.target.evaluation.map (d.towerUnit.app I)).app (op n)) := by
      rw [productMap_unit d T U I, ← DerivedCategory.Q.map_comp_assoc,
        ordinary_product_square d I, DerivedCategory.Q.map_comp]
      dsimp only [J]
      simp only [Category.assoc]
    _ = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫
          d.target.unit.app J ≫ d.target.limit.map (d.towerUnit.app I) ≫
            U.projection (d.tower.obj (DerivedCategory.Q.obj I)) := by
      have hn : d.target.limit.map (d.towerUnit.app I) ≫
          U.projection (d.tower.obj (DerivedCategory.Q.obj I)) =
          U.projection (DerivedCategory.Q.obj J) ≫
            Limits.Pi.map (fun n : ℕ ↦
              (d.target.evaluation.map (d.towerUnit.app I)).app (op n)) :=
        U.projection_natural (d.towerUnit.app I)
      dsimp only [J] at hn ⊢
      rw [hn]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫ f ≫
            Limits.Pi.map (fun n : ℕ ↦
              (d.target.evaluation.map (d.towerUnit.app I)).app (op n)))
        (projection_unit d.target U J).symm
    _ = _ := by
      dsimp only [J]
      simp only [Category.assoc]
      rw [← reassoc_of% d.comparison_unit I]


omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem productMap_naturality {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) {M N : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)} (f : M ⟶ N) :
    d.direct.map (Limits.Pi.map
        (fun n : ℕ ↦ (d.source.evaluation.map f).app (op n))) ≫ productMap d N =
      productMap d M ≫ Limits.Pi.map
        (fun n : ℕ ↦ (d.target.evaluation.map (d.tower.map f)).app (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productMap_π, productMap_π_assoc, Pi.map_π]
  rw [← d.direct.map_comp_assoc, Pi.map_π, d.direct.map_comp, Category.assoc]
  congr 1
  exact congr_app (d.evaluationIso.inv.naturality f) (op n)

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
  [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] in
private theorem derivedNatTrans_ext_on_KInjectives
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    {E : Type*} [Category E] {F₁ F₂ : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ E}
    (τ τ' : F₁ ⟶ F₂)
    (h : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
      τ.app (DerivedCategory.Q.obj I) = τ'.app (DerivedCategory.Q.obj I)) : τ = τ' := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  intro X
  let q := (CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ A)).app X
  let : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ A) X).2
  apply (cancel_mono (F₂.map (DerivedCategory.Q.map q))).mp
  rw [← τ.naturality, ← τ'.naturality, h _ inferInstance]

private def productTransformation {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) :
    d.source.evaluation ⋙ derivedProducts ⋙ d.direct ⟶
      d.tower ⋙ d.target.evaluation ⋙ derivedProducts where
  app := productMap d
  naturality _ _ f := productMap_naturality d f

private theorem projection_square {G : A ⥤ B} [G.Additive]
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.map (T.projection M) ≫ productMap d M =
      d.comparison.hom.app M ≫ U.projection (d.tower.obj M) := by
  have h : Functor.whiskerRight (projectionNat T) d.direct ≫ productTransformation d =
      d.comparison.hom ≫ Functor.whiskerLeft d.tower (projectionNat U) := by
    apply derivedNatTrans_ext_on_KInjectives
    intro I hI
    let := hI
    exact projection_square_on_KInjective d T U I
  exact congr_app h M

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasCountableProducts (DerivedCategory A)] in
private theorem roosProduct_isKInjective (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] : (roosP I).IsKInjective := by
  have (n : ℕ) : CochainComplex.IsKInjective (I.asFunctor.obj (op n)) :=
    tower_evaluation_isKInjective A I (op n)
  let K : ℕ → CochainComplex A ℤ := fun n ↦ I.asFunctor.obj (op n)
  obtain ⟨hki, _⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit K
  let := hki
  exact CochainComplex.isKInjective_of_iso
    ((HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K)).conePointUniqueUpToIso
      (limit.isLimit _))

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts
  (DerivedCategory A)] in
private theorem roosF_isKInjective (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] : (roosF.obj I).IsKInjective := by
  let := roosProduct_isKInjective I
  have hcone : (CochainComplex.mappingCone (roosU I)).IsKInjective := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished (roosU I))
      (CochainComplex.IsKInjective.rightOrthogonal (roosP I))
      (CochainComplex.IsKInjective.rightOrthogonal (roosP I))
  let := hcone
  exact inferInstanceAs ((CochainComplex.mappingCone (roosU I))⟦(-1 : ℤ)⟧).IsKInjective

omit [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
private theorem mappedInclusion_Q_isIso {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map (ordinaryInclusion I))) := by
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let := roosF_isKInjective I
  let := d.unit_isIso (ExactProductsRoos.ordinary.obj I) inferInstance
  let := d.unit_isIso (roosF.obj I) inferInstance
  let := ordinaryInclusion_Q_isIso d.source T I
  have he : DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map (ordinaryInclusion I)) =
        d.unit.app (ExactProductsRoos.ordinary.obj I) ≫
          d.direct.map (DerivedCategory.Q.map (ordinaryInclusion I)) ≫
            inv (d.unit.app (roosF.obj I)) := by
    rw [← unit_naturality_assoc d]
    simp
  rw [he]
  infer_instance

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasCountableProducts (DerivedCategory A)] [HasCountableProducts (DerivedCategory B)] in
private theorem additiveRoos_product_isIso (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsIso (piComparison (G.mapHomologicalComplex (.up ℤ))
      (fun n : ℕ ↦ X.asFunctor.obj (op n))) := by
  infer_instance

@[irreducible]
private def additiveRoosIso (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅
      roosF.obj
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) :=
  (strictRoosAdditiveComparison G (additiveRoos_product_isIso G)).choose X

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasCountableProducts (DerivedCategory A)] [HasCountableProducts (DerivedCategory B)] in
private theorem additiveRoosIso_coordinates (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (additiveRoosIso G X).hom.f (p + 1) ≫
        (roosχ
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) p).hom =
      G.map (roosχ X p).hom ≫ G.biprodComparison ((roosP X).X p)
        ((roosP X).X (p + 1)) ≫
          biprod.map ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
            ((piComparison (G.mapHomologicalComplex (.up ℤ))
              (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1)) := by
  unfold additiveRoosIso
  exact (strictRoosAdditiveComparison G (additiveRoos_product_isIso G)).choose_spec.1 X p


set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts (DerivedCategory A)] [HasCountableProducts (DerivedCategory B)] in
private theorem additiveRoosIso_inclusion {G : A ⥤ B} [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (d : DirectImageData G) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (ordinaryInclusion X) ≫
        (additiveRoosIso G X).hom =
      (NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app X ≫
        ordinaryInclusion
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change ((G.mapHomologicalComplex (.up ℤ)).map (ordinaryInclusion X) ≫
    (additiveRoosIso G X).hom).f (p + 1) =
      ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app X ≫
        ordinaryInclusion
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X)).f
          (p + 1)
  apply (cancel_mono
    (roosχ
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc,
    additiveRoosIso_coordinates, ordinaryInclusion_χ,
    Functor.mapHomologicalComplex_map_f]
  rw [← G.map_comp_assoc, ordinaryInclusion_χ]
  erw [map_biprod_lift, comp_biprod_lift]
  simp only [Functor.map_zero, zero_comp, comp_zero]
  congr 1
  simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] using
    congrArg (fun f ↦ f.f (p + 1)) (ordinary_product_square d X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasCountableProducts (DerivedCategory A)] [HasCountableProducts (DerivedCategory B)] in
private theorem additiveRoosIso_boundary (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (roosBoundary.app X) ≫
        ((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
          (additiveRoosIso G X).hom⟦(1 : ℤ)⟧' =
      piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
        roosBoundary.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) := by
  ext p
  apply (cancel_mono
    ((CochainComplex.shiftFunctorObjXIso (roosF.obj
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X))
        1 p (p + 1) rfl).hom ≫
      (roosχ
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex
          (.up ℤ)).obj X) p).hom)).mp
  simp only [HomologicalComplex.comp_f, Category.assoc,
    CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Functor.comp_obj,
    CochainComplex.shiftFunctor_obj_X', Functor.mapHomologicalComplex_map_f,
    Category.id_comp]
  repeat' erw [Category.id_comp]
  erw [additiveRoosIso_coordinates G X p]
  erw [← G.map_comp_assoc, roosBoundary_f_coordinates, roosBoundary_f_coordinates]
  erw [map_biprod_lift, comp_biprod_lift]
  simp only [Functor.map_id, Functor.map_zero, Category.id_comp,
    zero_comp, comp_zero]
  erw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem cone_comparison_on_KInjective {G : A ⥤ B} [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    d.unit.app (roosF.obj I) ≫ d.direct.map (T.coneComparison.hom.app I) ≫
        d.comparison.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (additiveRoosIso G I).hom ≫
        U.coneComparison.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I) ≫
          d.target.limit.map (d.towerUnit.app I) := by
  let J := (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  let := mappedInclusion_Q_isIso d T I
  apply (cancel_epi (DerivedCategory.Q.map
    ((G.mapHomologicalComplex (.up ℤ)).map (ordinaryInclusion I)))).mp
  calc
    _ = d.unit.app (ExactProductsRoos.ordinary.obj I) ≫
        d.direct.map (d.source.unit.app I) ≫
          d.comparison.hom.app (DerivedCategory.Q.obj I) := by
      rw [unit_naturality_assoc d (ordinaryInclusion I),
        ← d.direct.map_comp_assoc, T.normalization]
    _ = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫
          d.target.unit.app J ≫ d.target.limit.map (d.towerUnit.app I) :=
      d.comparison_unit I
    _ = _ := by
      rw [← U.normalization J]
      dsimp only [J]
      erw [Category.assoc, ← DerivedCategory.Q.map_comp_assoc,
        ← additiveRoosIso_inclusion d I, DerivedCategory.Q.map_comp]
      simp only [Category.assoc]



omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem productMap_shift {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.map (towerProductShift
        (fun n : ℕ ↦ (d.source.evaluation.obj M).map (homOfLE (Nat.le_succ n)).op)) ≫
        productMap d M =
      productMap d M ≫ towerProductShift
        (fun n : ℕ ↦ (d.target.evaluation.obj (d.tower.obj M)).map
          (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productMap_π, productMap_π_assoc,
    towerProductShift, Pi.lift_π]
  rw [← d.direct.map_comp_assoc, Pi.lift_π, d.direct.map_comp, Category.assoc]
  congr 1
  exact (d.evaluationIso.inv.app M).naturality (homOfLE (Nat.le_succ n)).op

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem productMap_difference {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) [d.direct.Additive]
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ (d.source.evaluation.obj M).map (homOfLE (Nat.le_succ n)).op)) ≫
        productMap d M =
      productMap d M ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ (d.target.evaluation.obj (d.tower.obj M)).map
          (homOfLE (Nat.le_succ n)).op) := by
  simp only [towerTransitionEndomorphism, Functor.map_sub, Functor.map_id,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id]
  rw [productMap_shift]

private def canonicalDerivedUnit (G : A ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions A] :
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  e.hom ≫ Functor.whiskerLeft π G.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      G.rightDerivedFunctor).hom

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasCountableProducts A] [HasCountableProducts (DerivedCategory
  A)] [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
private theorem canonicalDerivedUnit_isIso (G : A ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions A]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((canonicalDerivedUnit G).app I) := by
  dsimp [canonicalDerivedUnit]
  infer_instance

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasCountableProducts A] [HasCountableProducts (DerivedCategory
  A)] [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
private theorem canonicalDerivedUnit_isRightDerived (G : A ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions A] :
    G.rightDerivedFunctor.IsRightDerivedFunctor (canonicalDerivedUnit G)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    intro I J f hf
    have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
      (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
    have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
      (CochainComplex.KInjectives.toHomotopyCategory.map f)
    have hmap' : IsIso ((π ⋙ H).map f.hom) := hmap
    have heq : (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom =
        e.hom.app I.obj ≫ (π ⋙ H).map f.hom ≫ e.inv.app J.obj := by
      rw [← e.hom.naturality_assoc]
      simp
    change IsIso ((G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom)
    rw [heq]
    infer_instance
  exact h.isRightDerivedFunctor_of_isIso (canonicalDerivedUnit G) (fun I ↦ by
    have := I.property
    exact canonicalDerivedUnit_isIso G I.obj)

@[irreducible]
private def directIsoCanonical {G : A ⥤ B} [G.Additive]
    [Abelian.HasKInjectiveResolutions A] (d : DirectImageData G) :
    G.rightDerivedFunctor ≅ d.direct :=
  letI := d.direct_derived
  letI := canonicalDerivedUnit_isRightDerived G
  Functor.rightDerivedUnique G.rightDerivedFunctor d.direct
    (canonicalDerivedUnit G) d.unit (HomologicalComplex.quasiIso A (.up ℤ))

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
private theorem direct_additive {G : A ⥤ B} [G.Additive]
    [Abelian.HasKInjectiveResolutions A] (d : DirectImageData G) : d.direct.Additive := by
  exact Functor.additive_of_iso (directIsoCanonical d)

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem alpha_isIso {G : A ⥤ B} [G.Additive]
    [Abelian.HasKInjectiveResolutions A]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) : IsIso (alpha d M) := by
  let a := adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (directIsoCanonical d)
  let := a.isRightAdjoint
  dsimp [alpha]
  infer_instance

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
private theorem direct_commShift {G : A ⥤ B} [G.Additive]
    [Abelian.HasKInjectiveResolutions A]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (d : DirectImageData G) :
    ∃ h : d.direct.CommShift ℤ, letI := h; NatTrans.CommShift d.unit ℤ := by
  let := canonicalRightDerivedAdjunctionShift adj
  let := adj.commShift_rightDerivedFunctorUnit
  have hu : NatTrans.CommShift (canonicalDerivedUnit G) ℤ := by
    dsimp [canonicalDerivedUnit]
    infer_instance
  let := hu
  let e := directIsoCanonical d
  let := Functor.CommShift.ofIso e ℤ
  let := Functor.CommShift.ofIso_compatibility e ℤ
  have he : canonicalDerivedUnit G ≫ Functor.whiskerLeft DerivedCategory.Q e.hom =
      d.unit := by
    let := d.direct_derived
    let := canonicalDerivedUnit_isRightDerived G
    simpa only [e, directIsoCanonical, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Iso.refl_hom, Category.id_comp] using
        Functor.rightDerivedNatTrans_fac G.rightDerivedFunctor d.direct
          (canonicalDerivedUnit G) d.unit (HomologicalComplex.quasiIso A (.up ℤ))
          (𝟙 (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q))
  refine ⟨inferInstance, ?_⟩
  rw [← he]
  infer_instance

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
private theorem unit_shift {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    [d.direct.CommShift ℤ] [NatTrans.CommShift d.unit ℤ] (L : CochainComplex A ℤ) :
    d.unit.app (L⟦(1 : ℤ)⟧) ≫
        d.direct.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app L) ≫
        (d.direct.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj L) =
      DerivedCategory.Q.map
          (((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app L) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        (d.unit.app L)⟦(1 : ℤ)⟧' := by
  simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
    (NatTrans.shift_app_comm d.unit (1 : ℤ) L).symm

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts A]
  [HasCountableProducts (DerivedCategory A)] in
@[reassoc]
private theorem Q_shift_naturality {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    DerivedCategory.Q.map (f⟦(1 : ℤ)⟧') ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app Y =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app X ≫
        (DerivedCategory.Q.map f)⟦(1 : ℤ)⟧' :=
  (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality f

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
@[reassoc]
private theorem direct_shift_naturality {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) [d.direct.CommShift ℤ]
    {X Y : DerivedCategory.{w} A} (f : X ⟶ Y) :
    d.direct.map (f⟦(1 : ℤ)⟧') ≫ (d.direct.commShiftIso (1 : ℤ)).hom.app Y =
      (d.direct.commShiftIso (1 : ℤ)).hom.app X ≫ (d.direct.map f)⟦(1 : ℤ)⟧' :=
  (d.direct.commShiftIso (1 : ℤ)).hom.naturality f

@[reassoc]
private theorem boundary_model {L : LimitData.{w} A} (T : RoosTriangleData L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (T.productComparison X).hom ≫ T.boundary (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (roosBoundary.app X) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
          (T.coneComparison.hom.app X)⟦(1 : ℤ)⟧' :=
  T.boundary_model X

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasCountableProducts (DerivedCategory
  A)] [HasCountableProducts (DerivedCategory B)] in
private theorem additiveRoosIso_Q_boundary (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map (roosBoundary.app I)) ≫
        DerivedCategory.Q.map
          (((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app (roosF.obj I)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj (roosF.obj I)) ≫
        (DerivedCategory.Q.map (additiveRoosIso G I).hom)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ I.asFunctor.obj (op n))) ≫
        DerivedCategory.Q.map (roosBoundary.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          (roosF.obj
            ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)) := by
  rw [← Q_shift_naturality (additiveRoosIso G I).hom]
  simpa only [DerivedCategory.Q.map_comp, Category.assoc] using congrArg
    (fun f ↦ DerivedCategory.Q.map f ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (roosF.obj
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)))
    (additiveRoosIso_boundary G I)

private theorem boundary_square_on_KInjective {G : A ⥤ B} [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (d : DirectImageData G) [d.direct.Additive] [d.direct.CommShift ℤ]
    [NatTrans.CommShift d.unit ℤ]
    (T : RoosTriangleData d.source) (U : RoosTriangleData d.target)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    d.direct.map (T.boundary (DerivedCategory.Q.obj I)) ≫
        (d.direct.commShiftIso (1 : ℤ)).hom.app (d.source.limit.obj (DerivedCategory.Q.obj I)) ≫
        (d.comparison.hom.app (DerivedCategory.Q.obj I))⟦(1 : ℤ)⟧' =
      productMap d (DerivedCategory.Q.obj I) ≫
        U.boundary (d.tower.obj (DerivedCategory.Q.obj I)) := by
  let J := (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  let := roosProduct_isKInjective I
  let := d.unit_isIso (roosP I) inferInstance
  apply (cancel_epi (d.unit.app (roosP I) ≫
    d.direct.map (T.productComparison I).hom)).mp
  calc
    _ = d.unit.app (roosP I) ≫
        d.direct.map (DerivedCategory.Q.map (roosBoundary.app I)) ≫
        d.direct.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I)) ≫
        (d.direct.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (roosF.obj I)) ≫
        (d.direct.map (T.coneComparison.hom.app I) ≫
          d.comparison.hom.app (DerivedCategory.Q.obj I))⟦(1 : ℤ)⟧' := by
      simp only [Category.assoc]
      rw [← d.direct.map_comp_assoc, boundary_model T I,
        d.direct.map_comp, d.direct.map_comp]
      simp only [Category.assoc]
      have hs : d.direct.map ((T.coneComparison.hom.app I)⟦(1 : ℤ)⟧') ≫
          (d.direct.commShiftIso (1 : ℤ)).hom.app
            (d.source.limit.obj (DerivedCategory.Q.obj I)) =
          (d.direct.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (roosF.obj I)) ≫
            (d.direct.map (T.coneComparison.hom.app I))⟦(1 : ℤ)⟧' :=
        direct_shift_naturality d (T.coneComparison.hom.app I)
      rw [reassoc_of% hs]
      simp only [Functor.map_comp]
    _ = DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map (roosBoundary.app I)) ≫
        DerivedCategory.Q.map
          (((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app (roosF.obj I)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj (roosF.obj I)) ≫
        (DerivedCategory.Q.map (additiveRoosIso G I).hom ≫
          U.coneComparison.hom.app J ≫ d.target.limit.map (d.towerUnit.app I))⟦(1 : ℤ)⟧' := by
      erw [← unit_naturality_assoc d (roosBoundary.app I),
        reassoc_of% unit_shift d (roosF.obj I)]
      simp only [Functor.map_comp]
      rw [← Functor.map_comp, ← Functor.map_comp,
        cone_comparison_on_KInjective d T U I]
      dsimp only [J]
      simp only [Functor.map_comp]
    _ = DerivedCategory.Q.map (piComparison (G.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ I.asFunctor.obj (op n))) ≫
        (U.productComparison J).hom ≫ U.boundary (DerivedCategory.Q.obj J) ≫
        (d.target.limit.map (d.towerUnit.app I))⟦(1 : ℤ)⟧' := by
      simp only [Functor.map_comp]
      rw [reassoc_of% additiveRoosIso_Q_boundary G I]
      dsimp only [J]
      rw [← boundary_model_assoc U _]
    _ = _ := by
      simpa only [Category.assoc, Functor.comp_obj, J] using paste_boundary
        (productMap_unit d T U I) (U.boundary_natural (d.towerUnit.app I))


private theorem boundary_square {G : A ⥤ B} [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    (d : DirectImageData G) [d.direct.Additive] [d.direct.CommShift ℤ]
    [NatTrans.CommShift d.unit ℤ]
    (T : RoosTriangleData d.source) (U : RoosTriangleData d.target)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.map (T.boundary M) ≫
        (d.direct.commShiftIso (1 : ℤ)).hom.app (d.source.limit.obj M) ≫
        (d.comparison.hom.app M)⟦(1 : ℤ)⟧' =
      productMap d M ≫ U.boundary (d.tower.obj M) := by
  have h : Functor.whiskerRight (boundaryNat T) d.direct ≫
        Functor.whiskerLeft d.source.limit (d.direct.commShiftIso (1 : ℤ)).hom ≫
        Functor.whiskerRight d.comparison.hom (shiftFunctor _ (1 : ℤ)) =
      productTransformation d ≫ Functor.whiskerLeft d.tower (boundaryNat U) := by
    apply derivedNatTrans_ext_on_KInjectives
    intro I hI
    let := hI
    exact boundary_square_on_KInjective d T U I
  exact congr_app h M

private theorem tower_grothendieck
    (C₀ : Type*) [Category C₀] [Abelian C₀] [IsGrothendieckAbelian.{g} C₀] :
    IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ C₀) := by
  let G := separator C₀
  have hG := isSeparator_separator C₀
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint C₀ j).obj G) := by
    intro F F' f k hfk
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight C₀ j
    apply (adj.homEquiv G F').symm.injective
    have h := hfk _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a k).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ C₀) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{g, g} (ℕᵒᵖ ⥤ C₀) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{g, g} (ℕᵒᵖ ⥤ C₀) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f k h ↦ NatTrans.ext h)⟩ }

end PrivateSquares

end DirectImageRoosNormalization

open DirectImageRoosNormalization

/-- The normalized comparison is a morphism of the canonical Roos triangles.

Source: Stacks Project, Cohomology on Sites, Tag 0A07 (alternate proof) and Tag 0941;
Derived Categories, Tag 0BK6, with the explicit strict normalization in the DAG
(blueprint: lem-weil-pbc-direct-image-roos-normalization).

Proof plan:
1. Resolve M by a K-injective strict tower I with injective degree terms, using
   lem-weil-pbc-small-module-diagrams-grothendieck and
   lem-pur-kinjective-degreewise-existence. Evaluation preserves K-injectives by
   lem-weil-tower-evaluation-kinjective.
2. The exact adjoint F makes G and its tower functor preserve K-injectives
   (lem-weil-pbc-right-adjoint-preserves-kinjective); the same argument applies to
   inverse limit and its exact constant-tower left adjoint. Thus J = G(I), lim I and
   lim J compute all derived functors, by lem-weil-pbc-kinjective-total-derived.
3. Adjunction and the product and limit universal properties give the canonical
   chain isomorphisms c : G(product I) ≅ product J and β : G(lim I) ≅ lim J.
   Their legs are G of the original legs. Products of K-injectives represent derived
   products by lem-pc-ringed-space-product-kinjective. Projection to each factor shows
   that c commutes with s and hence 1-s.
4. By lem-weil-pbc-exact-products-roos-comparison, the ordinary-limit inclusions into
   the strict Roos cones give the unit-normalized identifications with Rlim.
   The change from its negative-difference fibre is (y,x) ↦ (-y,x), preserving the
   inclusion (0,λ). This yields the `RoosTriangleData` normalization on every complex.
5. Apply lem-pur-roos-additive-comparison to obtain the diagonal cone comparison θ.
   Its coordinates give θ G(j_I) = j_J β, c G(r_I) = r_J θ and the boundary square
   θ[1] G(b_I) = b_J c, including b(z) = (z,0).
6. The universal property of total derivation constructs σ, normalized by the units.
   On K-injectives it is the ordinary termwise shift identification; see
   lem-pc-right-derived-functor-triangulated. Thus the boundary square is the canonical
   connecting square, not merely a completion of the first two squares.
7. The unit equation from lem-weil-ringed-tower-pushforward-limit-comparison identifies
   a with β on I. Transport the three squares along the ordinary-limit inclusions.
   They hold for every derived strict tower by localization, with first component a. -/
theorem directImageRoosNormalization
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    (f : RingedToposMorphism R S) (_ringIso : IsIso f.ringMap)
    (F : ringedSiteModules.{u, u, u, u} S ⥤ ringedSiteModules.{u, u, u, u} R) [F.Additive]
    (_adj : F ⊣ f.modules) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)]
    [HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R))]
    [HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u} S)]
    (d : DirectImageData f.modules) :
    ∃ (T : RoosTriangleData d.source) (U : RoosTriangleData d.target)
      (σ : shiftFunctor (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)) (1 : ℤ) ⋙
        d.direct ≅
        d.direct ⋙ shiftFunctor (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S)) (1 : ℤ)),
      (∀ L : CochainComplex (ringedSiteModules.{u, u, u, u} R) ℤ,
        d.unit.app (L⟦(1 : ℤ)⟧) ≫
            d.direct.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app L) ≫
            σ.hom.app (DerivedCategory.Q.obj L) =
          DerivedCategory.Q.map
              (((f.modules.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app L) ≫
            (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
              ((f.modules.mapHomologicalComplex (.up ℤ)).obj L) ≫
            (d.unit.app L)⟦(1 : ℤ)⟧') ∧
      ∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R),
        IsIso (alpha d M) ∧
        (d.direct.map (towerProductShift
            (fun n : ℕ ↦ (d.source.evaluation.obj M).map (homOfLE (Nat.le_succ n)).op)) ≫
            productMap d M =
          productMap d M ≫ towerProductShift
            (fun n : ℕ ↦ (d.target.evaluation.obj (d.tower.obj M)).map
              (homOfLE (Nat.le_succ n)).op)) ∧
        (d.direct.map (T.projection M) ≫ productMap d M =
          d.comparison.hom.app M ≫ U.projection (d.tower.obj M)) ∧
        (d.direct.map (towerTransitionEndomorphism
            (fun n : ℕ ↦ (d.source.evaluation.obj M).map (homOfLE (Nat.le_succ n)).op)) ≫
            productMap d M =
          productMap d M ≫ towerTransitionEndomorphism
            (fun n : ℕ ↦ (d.target.evaluation.obj (d.tower.obj M)).map
              (homOfLE (Nat.le_succ n)).op)) ∧
        (d.direct.map (T.boundary M) ≫ σ.hom.app (d.source.limit.obj M) ≫
            (d.comparison.hom.app M)⟦(1 : ℤ)⟧' =
          productMap d M ≫ U.boundary (d.tower.obj M)) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let A := ringedSiteModules.{u, u, u, u} R
    let B := ringedSiteModules.{u, u, u, u} S
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian R
    let : IsGrothendieckAbelian.{u} B := SheafOfModules.isGrothendieckAbelian S
    let : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
    let : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ B) := tower_grothendieck B
    let : HasLimitsOfShape (Discrete ℕ) A := nat_products
    let : HasLimitsOfShape (Discrete ℕ) B := nat_products
    let : HasLimitsOfShape (Discrete ℕ) (DerivedCategory.{w} A) := nat_products
    let : HasLimitsOfShape (Discrete ℕ) (DerivedCategory.{w} B) := nat_products
    let : HasLimitsOfShape (Discrete ℕ) (CochainComplex A ℤ) := cochain_nat_products
    let : HasLimitsOfShape (Discrete ℕ) (CochainComplex B ℤ) := cochain_nat_products
    let := _adj.isRightAdjoint
    let := direct_additive d
    obtain ⟨hshift, hunit⟩ := direct_commShift F _adj d
    let := hshift
    let := hunit
    obtain ⟨T⟩ := normalizedRoosTriangle d.source
    obtain ⟨U⟩ := normalizedRoosTriangle d.target
    refine ⟨T, U, d.direct.commShiftIso (1 : ℤ), unit_shift d, ?_⟩
    intro M
    exact ⟨alpha_isIso F _adj d M, productMap_shift d M, projection_square d T U M,
      productMap_difference d M, boundary_square d T U M⟩

end CategoryTheory
