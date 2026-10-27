/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram
public import Sheaf.Paper.RingedScalarExtensionComplexAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite free scalar extension and the canonical strict derived limit

Source: blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md, (1), finite sums and derived inverse limits
(blueprint: lem-sp-field-scalar-strict-limit).

The small site is any chosen small model of the scheme's pro-etale site. All complexes
are unbounded. The scalar-first convention writes the paper's x tensor s as s tensor x.
The records below specify the canonical comparison, including both actual cone coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w t v uB vB
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RingedTensor

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- A ring-sheaf map together with the finite-free hypothesis, expressed by the existing
finite product (equivalently finite sum) of copies of the unit module. No basis is selected.
Source: blueprint field-extension-towers proof (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
abbrev FiniteFreeScalarArrow (R S : Sheaf J CommRingCat.{u}) :=
  {a : R ⟶ S // ∃ d : ℕ, Nonempty
    ((∏ᶜ fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction a).obj (unit (ringSheaf S)))}

variable [hD : ∀ R : Sheaf J CommRingCat.{u},
    HasDerivedCategory.{w} (ringedSiteModules.{u} (ringSheaf R))]
  [hDT : ∀ R : Sheaf J CommRingCat.{u},
    HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R))]

/-- Projection-normalized scalar/limit compatibility for one finite-free map.
All maps are module-sheaf maps over S, and hence S-linear. The ordinary normalization
and uniqueness exclude a choice of a triangle filler. The cone formula uses the same beta
on both coordinates with the canonical shifted-cone coordinates roosχ.
Source: blueprint field-extension-towers proof (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
structure ScalarStrictLimitComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (LR : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (LS : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (rhoR : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LR)
    (rhoS : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LS) where
  /-- Naturality is on the derived category of entire strict towers. -/
  comparison : LR ⋙ F.mapDerivedCategory ≅
    (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory ⋙ LS
  /-- The ordinary scalar/limit comparison fixes the derived map. -/
  normalized : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map ((roosDerivedUnit rhoR).app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map (limit.post X.asFunctor
          (F.mapHomologicalComplex (.up ℤ))) ≫
        (roosDerivedUnit rhoS).app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        LS.map ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.inv.app X)
  /-- The product map is the canonical map specified by all its projections. -/
  beta : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, (F.mapHomologicalComplex (.up ℤ)).obj (roosP X) ≅
    roosP (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)
  /-- Projection formula; in a finite basis this is finite-sum/product reindexing. -/
  beta_projection : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    (beta X).hom ≫ Pi.π _ n =
      (F.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n)
  /-- The product map intertwines one minus the transition shift. -/
  beta_transition : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (F.mapHomologicalComplex (.up ℤ)).map (roosU X) ≫ (beta X).hom =
      (beta X).hom ≫ roosU
        (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)
  /-- An actual natural chain isomorphism of the signed Roos cones. -/
  cone : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ roosF
  /-- First product coordinate of the actual cone map. -/
  cone_first : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (cone.hom.app X).f (p + 1) ≫
        (roosχ (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex
          (.up ℤ)).obj X) p).hom ≫ biprod.fst =
      F.map ((roosχ X p).hom ≫ biprod.fst) ≫ (beta X).hom.f p
  /-- Second product coordinate of the same cone map. -/
  cone_second : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (cone.hom.app X).f (p + 1) ≫
        (roosχ (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex
          (.up ℤ)).obj X) p).hom ≫ biprod.snd =
      F.map ((roosχ X p).hom ≫ biprod.snd) ≫ (beta X).hom.f (p + 1)
  /-- The cone map realizes precisely the canonical comparison in the derived category. -/
  cone_realizes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (rhoR.hom.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (cone.hom.app X) ≫
        rhoS.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        LS.map ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.inv.app X)



namespace FieldScalarStrictLimit

universe uA vA uD vD

/-- The existing exact derived functor with explicit exactness witnesses. This is only
an abbreviation, preventing repeated searches for an entire family of witnesses.
Source: blueprint field-extension-towers (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
abbrev exactDerived
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F) :
    DerivedCategory.{w} A ⥤ DerivedCategory.{w} B :=
  @Functor.mapDerivedCategory A _ _ _ B _ _ _ F _ hl hc

/-- The balanced derived associator is the existing localization of the ordinary one.
Source: blueprint field-extension-towers (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
def exactDerivedComp
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w} D]
    {F : A ⥤ B} [F.Additive] {G : B ⥤ D} [G.Additive] {H : A ⥤ D} [H.Additive]
    (hlF : PreservesFiniteLimits F) (hcF : PreservesFiniteColimits F)
    (hlG : PreservesFiniteLimits G) (hcG : PreservesFiniteColimits G)
    (hlH : PreservesFiniteLimits H) (hcH : PreservesFiniteColimits H)
    (alpha : F ⋙ G ≅ H) :
    exactDerived F hlF hcF ⋙ exactDerived G hlG hcG ≅ exactDerived H hlH hcH :=
  letI := hlF
  letI := hcF
  letI := hlG
  letI := hcG
  letI := hlH
  letI := hcH
  Functor.mapDerivedCategoryCompNatIso alpha

/-- The existing derived identity unitor, induced by the ordinary scalar unitor.
Source: blueprint field-extension-towers (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
def exactDerivedUnit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {F : A ⥤ A} [F.Additive]
    (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F)
    (alpha : F ≅ 𝟭 A) : exactDerived F hl hc ≅ 𝟭 (DerivedCategory.{w} A) :=
  letI := hl
  letI := hc
  Functor.mapDerivedCategoryNatIso alpha ≪≫ Functor.mapDerivedCategoryIdIso A

end FieldScalarStrictLimit
open FieldScalarStrictLimit

end SheafOfModules
