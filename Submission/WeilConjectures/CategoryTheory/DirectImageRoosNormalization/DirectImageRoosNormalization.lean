/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Submission.WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import Submission.WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import Submission.WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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


end PrivateTriangles

variable [HasCountableProducts (DerivedCategory.{w} B)]

variable [HasCountableProducts B]

section PrivateSquares

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts


omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)]
  [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
@[reassoc]
private theorem unit_naturality {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ d.unit.app Y =
      d.unit.app X ≫ d.direct.map (DerivedCategory.Q.map f) :=
  d.unit.naturality f

@[reassoc]
private theorem boundary_model {L : LimitData.{w} A} (T : RoosTriangleData L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (T.productComparison X).hom ≫ T.boundary (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (roosBoundary.app X) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
          (T.coneComparison.hom.app X)⟦(1 : ℤ)⟧' :=
  T.boundary_model X

end PrivateSquares

end DirectImageRoosNormalization

open DirectImageRoosNormalization

end CategoryTheory
