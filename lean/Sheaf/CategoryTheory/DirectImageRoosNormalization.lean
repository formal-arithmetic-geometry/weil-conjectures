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
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
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

universe u v w uA vA uB vB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory
namespace DirectImageRoosNormalization

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
  sorry

end CategoryTheory
