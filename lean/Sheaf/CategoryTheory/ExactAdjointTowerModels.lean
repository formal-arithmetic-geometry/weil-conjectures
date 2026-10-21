/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.ExactProductsRoosComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.RoosComplex

/-! # Simultaneous exact-adjoint tower models

Source: Stacks Project, Cohomology on Sites, Tag 0A07, first proof; Tags 0941,
079P, 08BJ, 0BK6, 070K and 070Y
(blueprint: lem-weil-pbc-exact-adjoint-tower-models).

The structures package the choices and assertions of the statement. In particular,
they do not choose any replacement or any derived functor from a bare existence axiom.
The positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vA vB uA uB w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Functor Opposite

namespace CategoryTheory.ExactAdjointTowerModels

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Applying a functor levelwise to a strict tower complex.
Source: Stacks Tag 0A07, tower-topos square
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
abbrev tower (G : A ⥤ B) [G.Additive] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- A total right derived functor with its universal unit, computed on K-injectives.
This only bundles the conclusion of the recorded K-injective total-derivation lemma.
Source: Stacks Tags 070K and 070Y
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure DerivedModel (H : CochainComplex A ℤ ⥤ CochainComplex B ℤ) where
  functor : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B
  unit : H ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  on_injectives : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

variable [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- The negative-difference fibre coordinates, ordered as (y,x).
Source: Stacks Tag 0941 and the explicit sign calculation in the node
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
def negativeCoordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ExactProductsRoos.fibre.obj X).X (p + 1) ≅
      (roosP X).X p ⊞ (roosP X).X (p + 1) :=
  (CochainComplex.mappingCone (-roosU X)).shiftFunctorObjXIso
      (-1) (p + 1) p (add_neg_cancel_right p 1).symm ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) p (p + 1) rfl ≪≫
      biprod.braiding _ _

/-- The signed, unit-normalized Roos conclusions for one of the two categories.
The sign isomorphism and both comparisons are natural on all strict tower complexes.
The final fields transport the rotated cone triangle along the actual map j.
Source: Stacks Tag 0941, including the sign convention of the strict Roos model
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure NormalizedRoos (L : DerivedModel (roosLimitFunctor (A := A))) where
  sign : ExactProductsRoos.fibre (B := A) ≅ roosF
  sign_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (sign.hom.app X).f (p + 1) ≫ (roosχ X p).hom =
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _)
  negative : ExactProductsRoos.fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.functor
  ordinary : ExactProductsRoos.ordinary (B := A) ≅ roosLimitFunctor
  ordinary_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (p : ℤ),
    ((ordinary.hom.app X) ≫ limit.π X.asFunctor (op n)).f p =
      limit.π (X.X p) (op n)
  inclusion_sign : ExactProductsRoos.comparison ≫ sign.hom =
    ordinary.hom ≫ roosInclusion
  negative_normalization :
    Functor.whiskerRight ExactProductsRoos.comparison DerivedCategory.Q ≫ negative.hom =
      Functor.whiskerRight ordinary.hom DerivedCategory.Q ≫ L.unit
  comparison : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.functor
  comparison_sign : comparison =
    isoWhiskerRight sign.symm DerivedCategory.Q ≪≫ negative
  normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.map (roosι X) ≫ comparison.hom.app X = L.unit.app X
  quasiIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) → QuasiIso (roosι I)
  triangle : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) →
    ∃ e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
        DerivedCategory.Q.obj (roosF.obj I),
      e.hom = DerivedCategory.Q.map (roosι I) ∧
      Triangle.mk
        (DerivedCategory.Q.map (roosι I ≫ roosProj I))
        (DerivedCategory.Q.map (roosU I))
        (DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU I)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
          e.inv⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory.{w} A)
  unit_triangle : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) →
    Triangle.mk
      ((comparison.inv.app I) ≫ DerivedCategory.Q.map (roosProj I))
      (DerivedCategory.Q.map (roosU I))
      (DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU I)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
        (comparison.hom.app I)⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory.{w} A)

variable [HasLimitsOfShape ℕᵒᵖ B] [HasCountableProducts B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- All simultaneous models and their canonical normalizations. The derived models
are choices with universal units; c and beta are fixed by their projection equations.
No exact-product assumption is used except in the last field.
Source: Stacks Tag 0A07, first proof, and Tags 0BK6 and 0941
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure Models (G : A ⥤ B) [G.Additive] where
  direct : DerivedModel (G.mapHomologicalComplex (.up ℤ))
  towerDirect : DerivedModel (tower G)
  sourceLimit : DerivedModel (roosLimitFunctor (A := A))
  targetLimit : DerivedModel (roosLimitFunctor (A := B))
  resolution : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I),
      QuasiIso q ∧ I.IsKInjective ∧ ∀ r : ℤ, Injective (I.X r)
  kInjective : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      ((tower G).obj I).IsKInjective ∧
      (∀ r : ℤ, Injective (((tower G).obj I).X r)) ∧
      (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n)) ∧
        CochainComplex.IsKInjective
          ((G.mapHomologicalComplex (.up ℤ)).obj (I.asFunctor.obj (op n)))) ∧
      CochainComplex.IsKInjective (limit I.asFunctor) ∧
      CochainComplex.IsKInjective (limit ((tower G).obj I).asFunctor) ∧
      (roosP I).IsKInjective ∧ (roosP ((tower G).obj I)).IsKInjective ∧
      CochainComplex.IsKInjective
        ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ∧
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj (roosP I))
  computes : ∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I),
    QuasiIso q → I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      (∃ e : DerivedCategory.Q.obj ((tower G).obj I) ≅
          towerDirect.functor.obj (DerivedCategory.Q.obj X),
        e.hom ≫ towerDirect.functor.map (DerivedCategory.Q.map q) =
          towerDirect.unit.app I) ∧
      (∃ e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
          sourceLimit.functor.obj (DerivedCategory.Q.obj X),
        e.hom ≫ sourceLimit.functor.map (DerivedCategory.Q.map q) =
          sourceLimit.unit.app I) ∧
      (∃ e : DerivedCategory.Q.obj (limit ((tower G).obj I).asFunctor) ≅
          targetLimit.functor.obj (towerDirect.functor.obj (DerivedCategory.Q.obj X)),
        e.hom ≫ targetLimit.functor.map (towerDirect.functor.map (DerivedCategory.Q.map q)) =
          targetLimit.unit.app ((tower G).obj I) ≫
            targetLimit.functor.map (towerDirect.unit.app I)) ∧
      (∃ e : DerivedCategory.Q.obj
            ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ≅
          direct.functor.obj (sourceLimit.functor.obj (DerivedCategory.Q.obj X)),
        e.hom ≫ direct.functor.map (sourceLimit.functor.map (DerivedCategory.Q.map q)) =
          direct.unit.app (limit I.asFunctor) ≫
            direct.functor.map (sourceLimit.unit.app I))
  products : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor
          (fun n : ℕ ↦ ((tower G).obj I).asFunctor.obj (op n))))))
  c : ExactProductsRoos.product ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    tower G ⋙ ExactProductsRoos.product
  beta : roosLimitFunctor ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    tower G ⋙ roosLimitFunctor
  c_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    c.hom.app X ≫ Pi.π (fun k : ℕ ↦ ((tower G).obj X).asFunctor.obj (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n)
  beta_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    beta.hom.app X ≫ limit.π ((tower G).obj X).asFunctor (op n) =
      (G.mapHomologicalComplex (.up ℤ)).map (limit.π X.asFunctor (op n))
  shift_commutes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map
        (towerProductShift (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
        c.hom.app X =
      c.hom.app X ≫ towerProductShift
        (fun n : ℕ ↦ ((tower G).obj X).asFunctor.map (homOfLE (Nat.le_succ n)).op)
  difference_commutes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map (roosU X) ≫ c.hom.app X =
      c.hom.app X ≫ roosU ((tower G).obj X)
  derived_product_components : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) → ∀ n : ℕ,
      DerivedCategory.Q.map (c.hom.app I) ≫
          DerivedCategory.Q.map
            (Pi.π (fun k : ℕ ↦ ((tower G).obj I).asFunctor.obj (op k)) n) ≫
          direct.unit.app (I.asFunctor.obj (op n)) =
        direct.unit.app (roosP I) ≫ direct.functor.map
          (DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n))
  localized_maps : ∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
    I.IsKInjective → I'.IsKInjective →
    (∀ a : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I',
      ∃ f : I ⟶ I', DerivedCategory.Q.map f = a) ∧
    (∀ (f g : I ⟶ I'), DerivedCategory.Q.map f = DerivedCategory.Q.map g →
      DerivedCategory.Q.map (roosPmap f) = DerivedCategory.Q.map (roosPmap g) ∧
      DerivedCategory.Q.map (roosLimitFunctor.map f) =
        DerivedCategory.Q.map (roosLimitFunctor.map g) ∧
      DerivedCategory.Q.map ((ExactProductsRoos.product ⋙
        G.mapHomologicalComplex (.up ℤ)).map f) =
        DerivedCategory.Q.map ((ExactProductsRoos.product ⋙
          G.mapHomologicalComplex (.up ℤ)).map g) ∧
      DerivedCategory.Q.map ((tower G ⋙ ExactProductsRoos.product).map f) =
        DerivedCategory.Q.map ((tower G ⋙ ExactProductsRoos.product).map g) ∧
      DerivedCategory.Q.map ((roosLimitFunctor ⋙
        G.mapHomologicalComplex (.up ℤ)).map f) =
        DerivedCategory.Q.map ((roosLimitFunctor ⋙
          G.mapHomologicalComplex (.up ℤ)).map g) ∧
      DerivedCategory.Q.map ((tower G ⋙ roosLimitFunctor).map f) =
        DerivedCategory.Q.map ((tower G ⋙ roosLimitFunctor).map g))
  exact_products : HasExactLimitsOfShape (Discrete ℕ) A →
    HasExactLimitsOfShape (Discrete ℕ) B →
      Nonempty (NormalizedRoos sourceLimit) ∧ Nonempty (NormalizedRoos targetLimit)

/-- The simultaneous tower, product and inverse-limit models for an exact adjoint pair.
Source: Stacks Project, Tag 0A07, first proof via the tower-topos square;
Tags 079P, 08BJ, 0BK6, 070K, 070Y and 0941
(blueprint: lem-weil-pbc-exact-adjoint-tower-models).

Proof plan:
1. Module sheaves and their small diagram categories are Grothendieck abelian
   (lem-weil-pbc-ring-sheaves-grothendieck,
   lem-weil-pbc-small-module-diagrams-grothendieck). Apply
   lem-pur-kinjective-degreewise-existence to get degreewise-injective resolutions.
2. Products and ordinary limits exist sectionwise; compatible families glue
   componentwise. Differentials are induced by their universal properties.
3. The pointwise adjunction has exact left adjoint by
   lem-weil-tower-category-levelwise-abelian. Apply
   lem-weil-pbc-right-adjoint-preserves-kinjective and
   lem-sp-right-adjoint-preserves-injectives to its right adjoint.
4. Evaluation preserves K-injectives (lem-weil-tower-evaluation-kinjective).
   The exact constant-tower left adjoint makes limit preserve K-injectives.
   Apply the same exact-adjoint criterion to G after taking limits.
5. Apply lem-pc-ringed-space-product-kinjective to both level families. It also
   supplies the localized product universal properties. Apply G once more.
6. Use lem-weil-pbc-kinjective-total-derived for G, its tower functor and both
   limits. Their units are invertible on K-injectives; naturality along q gives
   all four displayed computation isomorphisms.
7. Right adjoints preserve products and limits
   (lem-weil-pbc-right-adjoint-preserves-limits). Projection uniqueness gives
   c, beta, their chain-map equations and naturality on every tower complex.
8. Naturality of the universal unit identifies the components of Q(c) with
   RG of each projection. Projectionwise, both shift composites have component
   G(t_n)G(pi_(n+1)); additivity gives the difference equation.
9. Additive functors preserve chain homotopies. The Hom bijection of
   lem-weil-pbc-kinjective-hom-derived supplies all localized morphisms and
   independence of chain representatives, hence localized naturality.
10. Assuming exact products only now, lem-weil-derived-limit-roos-complex
    makes the prescribed j=(0,lambda) a quasi-isomorphism for I and J.
11. Apply lem-weil-pbc-exact-products-roos-comparison. The chain sign map
    (y,x)↦(-y,x) from the negative-difference fibre carries its inclusion to j.
    Compose its inverse with that normalized comparison to obtain kappa;
    thus Q(j) followed by kappa is precisely the universal limit unit.
12. The inverse rotation of the cone triangle has arrows r,1-s,b. Localize
    and transport its first object along Q(j). Its first arrow is Q(lambda)
    and its last is the localized b followed by the inverse shifted Q(j).
    The unit identity identifies this with the unit-normalized Roos triangle. -/
theorem exists_models
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (τ : GrothendieckTopology C) (σ : GrothendieckTopology D)
    (R : Sheaf τ RingCat.{u}) (S : Sheaf σ RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    (F : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S)
    [F.Additive] [G.Additive] (adj : F ⊣ G)
    (hF : ∀ E : ShortComplex (ringedSiteModules.{u} S),
      E.ShortExact → (E.map F).ShortExact) :
    Nonempty (Models G) := by
  sorry

end CategoryTheory.ExactAdjointTowerModels
