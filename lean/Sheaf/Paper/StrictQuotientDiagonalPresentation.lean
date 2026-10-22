/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
/-! # Section-normalized strict quotient presentations

The ordinary diagram-site data and its canonical derived representative comparison.
Source: Stacks Project, Tags 03DA, 03EK, 06YY and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

attribute [local irreducible] derivedExtension strictLimit quotientPresentation
  HasDerivedCategory.standard Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  constantSheaf SheafOfModules.monoidalCategory DerivedCategory
attribute [local instance 2000] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

/-- Standard localization for constant-coefficient module towers.
This is the standard derived-category instance, without a global-sections construction.
Source: Stacks 05RU, 0940 (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
instance strictQuotientTowerHasDerived (O : Sheaf J CommRingCat.{u}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ Mod O) :=
  HasDerivedCategory.standard _

/-- The published constant ring on the vertical sequence site.
Source: Stacks 0940 (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def strictDiagonalRing : Sheaf (WeilConjectures.coefficientSequenceTopology J)
    CommRingCat.{u} :=
  SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
    ((Functor.const ℕᵒᵖ).obj (constant J A))

/-- The published quotient ring on that site, with the actual quotient transitions.
Source: Stacks 0940, 099M (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def strictQuotientRing : Sheaf (WeilConjectures.coefficientSequenceTopology J)
    CommRingCat.{u} :=
  SheafOfModules.systemSequenceRing.{u, u, u} (J := J) (finiteSystem J A I)

/-- Section-normalized ordinary data for the strict quotient realization.
All categories and scalar operations are existing constructions. The fields fix the
coefficient map, the constant-tower equivalence, the diagonal and the scalar insertion;
they do not assume any derived comparison or completion assertion.
Source: Stacks 0940 and 03CZ; strict quotient auxiliary
(blueprint: def-pur-strict-quotient-diagonal-presentation). -/
structure StrictQuotientDiagonalPresentation where
  /-- The structural map Delta A to the quotient coefficient sheaf. -/
  ringMap : strictDiagonalRing J A ⟶ strictQuotientRing J A I
  /-- Its sections are the actual maps A to A/I^(n+1). -/
  ringMap_sections : ∀ (n : ℕ) (U : Cᵒᵖ),
    HEq (ringMap.hom.app (op (n, U.unop))) ((quotient J A I n).hom.app U)
  /-- Constant-ring sequence modules are ordinary strict A-module towers. -/
  towers : Mod (strictDiagonalRing J A) ≌ (ℕᵒᵖ ⥤ Mod (constant J A))
  /-- The equivalence is additive. -/
  [towers_additive : towers.functor.Additive]
  /-- Its component modules are the literal vertical restrictions. -/
  towers_objects : ∀ (M : Mod (strictDiagonalRing J A)) (n : ℕ) (U : Cᵒᵖ),
    HEq (((towers.functor.obj M).obj (op n)).val.obj U) (M.val.obj (op (n, U.unop)))
  /-- Its vertical arrows are the original vertical restrictions. -/
  towers_restrictions : ∀ (M : Mod (strictDiagonalRing J A)) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V),
    HEq (((towers.functor.obj M).obj (op n)).val.map f)
      (M.val.map (Prod.mkHom (𝟙 n) f.unop).op)
  /-- Its horizontal arrows are the original horizontal restrictions. -/
  towers_transitions : ∀ (M : Mod (strictDiagonalRing J A)) {m n : ℕ}
    (h : m ≤ n) (U : Cᵒᵖ),
    HEq (((towers.functor.obj M).map (homOfLE h).op).val.app U)
      (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  /-- It leaves every component of a module morphism unchanged. -/
  towers_maps : ∀ {M N : Mod (strictDiagonalRing J A)} (f : M ⟶ N)
    (n : ℕ) (U : Cᵒᵖ),
    HEq (((towers.functor.map f).app (op n)).val.app U) (f.val.app (op (n, U.unop)))
  /-- The ordinary diagonal on the ringed sequence site. -/
  diagonal : Mod (constant J A) ⥤ Mod (strictDiagonalRing J A)
  /-- The diagonal is additive. -/
  [diagonal_additive : diagonal.Additive]
  /-- The diagonal is exact on kernels. -/
  [diagonal_limits : PreservesFiniteLimits diagonal]
  /-- The diagonal is exact on cokernels. -/
  [diagonal_colimits : PreservesFiniteColimits diagonal]
  /-- Diagonal sections retain the entire module structure. -/
  diagonal_objects : ∀ (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ),
    HEq ((diagonal.obj M).val.obj (op (n, U.unop))) (M.val.obj U)
  /-- All diagonal restrictions are the vertical restrictions of M. -/
  diagonal_restrictions : ∀ (M : Mod (constant J A))
    {X Y : (ℕ × C)ᵒᵖ} (f : X ⟶ Y),
    HEq ((diagonal.obj M).val.map f) (M.val.map f.unop.2.op)
  /-- Diagonal maps are unchanged on sections. -/
  diagonal_maps : ∀ {M N : Mod (constant J A)} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
    HEq ((diagonal.map f).val.app (op (n, U.unop))) (f.val.app U)
  /-- The ordinary scalar-insertion map before localization. -/
  insertion : diagonal ⟶ diagonal ⋙ change ringMap ⋙ res ringMap
  /-- Scalar insertion is x mapped to 1 tensor x, followed by sheafification. -/
  insertion_sections : ∀ (M : Mod (constant J A)) (X : (ℕ × C)ᵒᵖ)
    (x : (diagonal.obj M).val.obj X),
    (insertion.app M).val.app X x = tensorSection ringMap (diagonal.obj M) X 1 x
  /-- Scalar restriction of the whole tensor diagram is the published quotient tower. -/
  reductionIso : diagonal ⋙ change ringMap ⋙ res ringMap ⋙ towers.functor ≅
    reductionTower J A I false
  /-- This comparison is the identity on the local pure tensors at every level. -/
  reductionIso_sections : ∀ (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ)
    (s : (finite J A I n).obj.obj U)
    (x : (diagonal.obj M).val.obj (op (n, U.unop))) (m : M.val.obj U)
    (z : ((towers.functor.obj ((res ringMap).obj
      ((change ringMap).obj (diagonal.obj M)))).obj (op n)).val.obj U),
    HEq x m → HEq z (tensorSection ringMap (diagonal.obj M) (op (n, U.unop)) s x) →
      (((reductionIso.hom.app M).app (op n)).val.app U) z =
        tensorSection (quotient J A I n) M U s m
  /-- The canonical derived restriction, stored without expanding its composite. -/
  restrictionModel : D (strictQuotientRing J A I) ⥤ TD (constant J A)
  /-- This model is exactly the original composite of derived exact functors. -/
  restrictionModel_eq : restrictionModel =
    (res ringMap).mapDerivedCategory ⋙ towers.functor.mapDerivedCategory
  /-- The canonical derived reduction, stored without expanding its composite. -/
  reductionModel : D (constant J A) ⥤ D (strictQuotientRing J A I)
  /-- This model is exactly diagonal followed by the existing scalar extension. -/
  reductionModel_eq : reductionModel = diagonal.mapDerivedCategory ⋙ extend ringMap

attribute [instance] StrictQuotientDiagonalPresentation.towers_additive
  StrictQuotientDiagonalPresentation.diagonal_additive
  StrictQuotientDiagonalPresentation.diagonal_limits
  StrictQuotientDiagonalPresentation.diagonal_colimits

/-- Compose four ordinary-to-derived comparison squares.
Source: naturality and whiskering
(blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def fourComparisons
    {A₀ A₁ A₂ A₃ A₄ D₀ D₁ D₂ D₃ D₄ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {Q₀ : A₀ ⥤ D₀} {Q₁ : A₁ ⥤ D₁} {Q₂ : A₂ ⥤ D₂}
    {Q₃ : A₃ ⥤ D₃} {Q₄ : A₄ ⥤ D₄}
    {F₀ : A₀ ⥤ A₁} {F₁ : A₁ ⥤ A₂} {F₂ : A₂ ⥤ A₃} {F₃ : A₃ ⥤ A₄}
    {G₀ : D₀ ⥤ D₁} {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₃ ⥤ D₄}
    (α₀ : Q₀ ⋙ G₀ ⟶ F₀ ⋙ Q₁) (α₁ : Q₁ ⋙ G₁ ⟶ F₁ ⋙ Q₂)
    (α₂ : Q₂ ⋙ G₂ ⟶ F₂ ⋙ Q₃) (α₃ : Q₃ ⋙ G₃ ⟶ F₃ ⋙ Q₄) :
    Q₀ ⋙ G₀ ⋙ G₁ ⋙ G₂ ⋙ G₃ ⟶ F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃ ⋙ Q₄ :=
  Functor.whiskerRight
    (Functor.whiskerRight α₀ G₁ ≫ Functor.whiskerLeft F₀ α₁) (G₂ ⋙ G₃) ≫
    Functor.whiskerLeft (F₀ ⋙ F₁) (Functor.whiskerRight α₂ G₃) ≫
    Functor.whiskerLeft (F₀ ⋙ F₁ ⋙ F₂) α₃

/-- The component formula for comparison-square composition.
Source: definitions (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
theorem fourComparisons_app
    {A₀ A₁ A₂ A₃ A₄ D₀ D₁ D₂ D₃ D₄ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {Q₀ : A₀ ⥤ D₀} {Q₁ : A₁ ⥤ D₁} {Q₂ : A₂ ⥤ D₂}
    {Q₃ : A₃ ⥤ D₃} {Q₄ : A₄ ⥤ D₄}
    {F₀ : A₀ ⥤ A₁} {F₁ : A₁ ⥤ A₂} {F₂ : A₂ ⥤ A₃} {F₃ : A₃ ⥤ A₄}
    {G₀ : D₀ ⥤ D₁} {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₃ ⥤ D₄}
    (α₀ : Q₀ ⋙ G₀ ⟶ F₀ ⋙ Q₁) (α₁ : Q₁ ⋙ G₁ ⟶ F₁ ⋙ Q₂)
    (α₂ : Q₂ ⋙ G₂ ⟶ F₂ ⋙ Q₃) (α₃ : Q₃ ⋙ G₃ ⟶ F₃ ⋙ Q₄) (X : A₀) :
    (fourComparisons α₀ α₁ α₂ α₃).app X =
      (G₂ ⋙ G₃).map (G₁.map (α₀.app X) ≫ α₁.app (F₀.obj X)) ≫
      G₃.map (α₂.app (F₁.obj (F₀.obj X))) ≫
      α₃.app (F₂.obj (F₁.obj (F₀.obj X))) := by
  simp only [fourComparisons, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj]

private theorem fourComparisons_app_isIso
    {A₀ A₁ A₂ A₃ A₄ D₀ D₁ D₂ D₃ D₄ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {Q₀ : A₀ ⥤ D₀} {Q₁ : A₁ ⥤ D₁} {Q₂ : A₂ ⥤ D₂}
    {Q₃ : A₃ ⥤ D₃} {Q₄ : A₄ ⥤ D₄}
    {F₀ : A₀ ⥤ A₁} {F₁ : A₁ ⥤ A₂} {F₂ : A₂ ⥤ A₃} {F₃ : A₃ ⥤ A₄}
    {G₀ : D₀ ⥤ D₁} {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₃ ⥤ D₄}
    (α₀ : Q₀ ⋙ G₀ ⟶ F₀ ⋙ Q₁) (α₁ : Q₁ ⋙ G₁ ⟶ F₁ ⋙ Q₂)
    (α₂ : Q₂ ⋙ G₂ ⟶ F₂ ⋙ Q₃) (α₃ : Q₃ ⋙ G₃ ⟶ F₃ ⋙ Q₄) (X : A₀)
    [IsIso (α₀.app X)] [IsIso (α₁.app (F₀.obj X))]
    [IsIso (α₂.app (F₁.obj (F₀.obj X)))]
    [IsIso (α₃.app (F₂.obj (F₁.obj (F₀.obj X))))] :
    IsIso ((fourComparisons α₀ α₁ α₂ α₃).app X) := by
  rw [fourComparisons_app]
  infer_instance

attribute [local instance] fourComparisons_app_isIso

attribute [local irreducible] fourComparisons

namespace StrictQuotientDiagonalPresentation

variable {J A I} (d : StrictQuotientDiagonalPresentation J A I)

/-- The actual exact restriction from quotient systems to constant-A towers.
Source: Stacks 03CZ, 0940 (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
abbrev restriction := res d.ringMap ⋙ d.towers.functor

/-- The exact diagonal on ordinary derived categories.
Source: Stacks 0940 (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def diagonalD : D (constant J A) ⥤ D (strictDiagonalRing J A) :=
  d.diagonal.mapDerivedCategory

/-- Derived scalar restriction, followed by the existing constant-tower realization.
Source: Stacks 03CZ, 0940 (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def restrictionD : D (strictQuotientRing J A I) ⥤ TD (constant J A) :=
  d.restrictionModel

/-- Derived quotient reduction is S Delta, with S the existing universal scalar extension.
Source: Stacks 06YY, 099M (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def reductionD : D (constant J A) ⥤ D (strictQuotientRing J A I) :=
  d.reductionModel

/-- Identify the saved restriction model with its canonical exact composite.
Source: the defining equation (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def restrictionDIso :
    d.restrictionD ≅ (res d.ringMap).mapDerivedCategory ⋙
      d.towers.functor.mapDerivedCategory :=
  eqToIso d.restrictionModel_eq

/-- Identify the saved reduction model with its canonical scalar-extension composite.
Source: the defining equation (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def reductionDIso : d.reductionD ≅ d.diagonalD ⋙ extend d.ringMap :=
  eqToIso d.reductionModel_eq

/-- The canonical natural comparison before choosing a representative.
Source: Stacks 06YY, 0940
(blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def representativeTransformation :
    Q (constant J A) ⋙ (d.reductionD ⋙ d.restrictionD) ⟶
      (reductionTower J A I false).mapHomologicalComplex (.up ℤ) ⋙ TQ (constant J A) := by
  let := reductionTower_additive J A I false
  exact Functor.whiskerLeft (Q (constant J A))
      ((Functor.isoWhiskerRight d.reductionDIso d.restrictionD) ≪≫
        Functor.isoWhiskerLeft (d.diagonalD ⋙ extend d.ringMap) d.restrictionDIso ≪≫
        Functor.associator d.diagonalD (extend d.ringMap)
          ((res d.ringMap).mapDerivedCategory ⋙
            d.towers.functor.mapDerivedCategory)).hom ≫
    fourComparisons
      (G₀ := d.diagonal.mapDerivedCategory) (G₁ := extend d.ringMap)
      (G₂ := (res d.ringMap).mapDerivedCategory)
      (G₃ := d.towers.functor.mapDerivedCategory)
      d.diagonal.mapDerivedCategoryFactors.hom
      (extendComparison d.ringMap) (res d.ringMap).mapDerivedCategoryFactors.hom
      d.towers.functor.mapDerivedCategoryFactors.hom ≫
    Functor.whiskerRight
      ((Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (d.diagonal.mapHomologicalComplex (.up ℤ))
            (Functor.mapHomologicalComplexCompIso
              (F := change d.ringMap) (G := res d.ringMap) (Iso.refl _) (.up ℤ)) ≪≫
            Functor.mapHomologicalComplexCompIso
              (F := d.diagonal) (G := change d.ringMap ⋙ res d.ringMap)
              (Iso.refl _) (.up ℤ))
          (d.towers.functor.mapHomologicalComplex (.up ℤ))) ≪≫
        Functor.mapHomologicalComplexCompIso
        (F := d.diagonal ⋙ change d.ringMap ⋙ res d.ringMap)
        (G := d.towers.functor) (H := reductionTower J A I false)
        d.reductionIso (.up ℤ)).hom
      (TQ (constant J A))

/-- The canonical comparison to the strict quotient complex on one representative.
It is built from the exact diagonal, universal scalar-extension counit, exact scalar
restriction, exact tower equivalence, and the section-normalized ordinary tensor comparison.
Source: Stacks 06YY, 0940 (blueprint: def-pur-strict-quotient-diagonal-presentation). -/
def representative (P : Cx (constant J A)) :
    (d.reductionD ⋙ d.restrictionD).obj ((Q (constant J A)).obj P) ⟶
      (TQ (constant J A)).obj (reductionComplex J A I false P) :=
  d.representativeTransformation.app P


/-- The representative is invertible whenever its scalar-extension comparison is.
Source: compose the four comparison squares and the ordinary reduction isomorphism
(blueprint: def-pur-strict-quotient-diagonal-presentation). -/
theorem representative_isIso_of_comparison (P : Cx (constant J A))
    [IsIso ((extendComparison d.ringMap).app
      ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P))] :
    IsIso (d.representative P) := by
  let := reductionTower_additive J A I false
  dsimp only [representative, representativeTransformation, diagonalD, restrictionD, reductionD, id]
  simp only [NatTrans.comp_app]
  infer_instance

attribute [irreducible] representativeTransformation

end StrictQuotientDiagonalPresentation

end CategoryTheory.ConstantCompletion
