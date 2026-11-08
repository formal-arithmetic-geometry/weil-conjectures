/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
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
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import Submission.WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Submission.WeilConjectures.Algebra.Homology.RoosComplex
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Adjunction units and normalized signed Roos comparisons

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Tags 09BN and 09BP;
blueprint prop-sf-pf-coherence, open-factor base-change paragraph
(blueprint: lem-sf-roos-adjunction-unit-coherence).

The record below bundles the specified comparisons together with their equations.
Its fields are conclusions, not extra assumptions of the theorem. The underlying Roos
functor is the existing shifted cone. The signed coordinates put the unshifted product
first, with differential (dx,(1-s)x-dy). The same normalized theta is used for both
functors; every augmentation is an actual chain map with zero second coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uA vA uB vB wA wB uC vC r uD vD s

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RoosAdjunctionUnit

/-- Localize the specified degreewise adjunction using the standard exact-functor
factorizations. Both units and counits are the localized original maps.
Source: Stacks Project, Tag 015F (blueprint: lem-sf-roos-adjunction-unit-coherence).
This helper extends the recorded construction to independent universes; its common-universe
specialization is identified by `exactDerivedAdjunctionUniverses_commonUniverses`. -/
def exactDerivedAdjunctionUniverses
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

section Helpers
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]

/-- Transparent termwise application on strict tower complexes.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerComplex (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)

/-- The standard exact localization of termwise application on strict towers.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerDerived [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The standard localization factorization for termwise tower application.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerFactors [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The specified exact derived adjunction on strict towers.
Source: Stacks 015F, 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
def towerAdjunction [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    towerDerived F ⊣ towerDerived G :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exactDerivedAdjunctionUniverses (a.whiskerRight ℕᵒᵖ)

/-- Signed coordinates (x,y)=(u,-v) on the existing shifted Roos cone.
Source: Stacks 0941; the signed normalization of exactProductFunctorStrictLimit
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
def coordinates [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p :=
  roosχ X p ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso (Iso.refl _) {
      hom := -𝟙 _
      inv := -𝟙 _
      hom_inv_id := by simp
      inv_hom_id := by simp }

end Helpers

section Statement
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasLimits A] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
  (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
  (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
  (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
    DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
  (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
    DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)

/-- The comparisons and all conclusions of the adjunction-unit calculation, in one
record. In particular, kappa is specified on both signed product coordinates; theta
is natural and has the ordinary-limit inclusion normalization on K-injectives; lambda
is exactly its conjugate of kappa. No cone filler or arbitrary comparison is an input.
Source: Stacks 0941, 09BN, 09BP and the open-factor calculation in prop-sf-pf-coherence
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
structure Coherence where
  thetaA : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q
  thetaB : DerivedCategory.Q ⋙ LB ≅ roosF ⋙ DerivedCategory.Q
  normalizationA : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
    (∀ p : ℤ, Injective (I.X p)) →
    etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.map (roosι I)
  normalizationB : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective],
    (∀ p : ℤ, Injective (I.X p)) →
    etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.map (roosι I)
  kappaF : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF
  kappaG : roosF ⋙ G.mapHomologicalComplex (.up ℤ) ≅ towerComplex G ⋙ roosF
  kappaF_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (kappaF.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex F).obj X) p).hom =
      F.map (coordinates X p).hom ≫
        F.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  kappaG_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ),
    (kappaG.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex G).obj X) p).hom =
      G.map (coordinates X p).hom ≫
        G.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map
          ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  lambdaF : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB
  lambdaG : LB ⋙ G.mapDerivedCategory ≅ towerDerived G ⋙ LA
  lambdaF_normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (thetaA.hom.app X) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappaF.hom.app X) =
      lambdaF.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((towerFactors F).hom.app X) ≫ thetaB.hom.app ((towerComplex F).obj X)
  lambdaG_normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
    G.mapDerivedCategory.map (thetaB.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappaG.hom.app X) =
      lambdaG.hom.app (DerivedCategory.Q.obj X) ≫
        LA.map ((towerFactors G).hom.app X) ≫ thetaA.hom.app ((towerComplex G).obj X)
  product_unit : ∀ M : ℕ → A,
    a.unit.app (∏ᶜ M) ≫ G.map (piComparison F M) ≫
        piComparison G (fun n : ℕ ↦ F.obj (M n)) =
      Limits.Pi.map (fun n : ℕ ↦ a.unit.app (M n))
  chain_unit : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
        kappaG.hom.app ((towerComplex F).obj X) =
      roosF.map (((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X)
  towerUnit : 𝟭 (DerivedCategory.{wA} (ℕᵒᵖ ⥤ A)) ≅ towerDerived F ⋙ towerDerived G
  towerUnit_hom : towerUnit.hom = (towerAdjunction a).unit
  derived_unit : ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A),
    (exactDerivedAdjunctionUniverses a).unit.app (LA.obj M) ≫
        G.mapDerivedCategory.map (lambdaF.hom.app M) ≫
        lambdaG.hom.app ((towerDerived F).obj M) ≫ LA.map (towerUnit.inv.app M) =
      𝟙 (LA.obj M)
  augmentation : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)),
    (∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) →
    ∃ (b : P ⟶ roosF.obj X)
      (bGF : (G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        roosF.obj ((towerComplex G).obj ((towerComplex F).obj X))),
      (∀ p : ℤ, b.f (p + 1) ≫ (coordinates X p).hom =
        biprod.lift ((Pi.lift gamma).f (p + 1)) 0) ∧
      (∀ p : ℤ, bGF.f (p + 1) ≫
        (coordinates ((towerComplex G).obj ((towerComplex F).obj X)) p).hom =
        biprod.lift ((Pi.lift (fun n : ℕ ↦
          (G.mapHomologicalComplex (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map (gamma n)))).f (p + 1)) 0) ∧
      b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
          kappaG.hom.app ((towerComplex F).obj X) =
        (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫ bGF ∧
      (∀ p : ℤ,
        (b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
          kappaG.hom.app ((towerComplex F).obj X)).f (p + 1) ≫
            (coordinates ((towerComplex G).obj ((towerComplex F).obj X)) p).hom =
        biprod.lift ((Pi.lift (fun n : ℕ ↦ gamma n ≫
          (a.mapHomologicalComplex (.up ℤ)).unit.app (X.asFunctor.obj (op n)))).f (p + 1)) 0) ∧
      (exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategory.map
            (DerivedCategory.Q.map b ≫ thetaA.inv.app X)) ≫
          G.mapDerivedCategory.map (lambdaF.hom.app (DerivedCategory.Q.obj X)) ≫
          lambdaG.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
          LA.map (towerUnit.inv.app (DerivedCategory.Q.obj X)) =
        DerivedCategory.Q.map b ≫ thetaA.inv.app X

end Statement

section ProofHelpers
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

end ProofHelpers

section DerivedCalculation
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]

end DerivedCalculation

end CategoryTheory.RoosAdjunctionUnit
