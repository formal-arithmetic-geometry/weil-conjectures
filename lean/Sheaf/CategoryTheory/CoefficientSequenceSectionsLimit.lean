/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Derived sections and total inverse limit of strict coefficient systems

Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E; Injectives, Tag 079P
(blueprint: lem-coef-sequence-sections-limit-comparison).

The direct image of the specified ringed sequence projection is inverse limit after
termwise restriction. Its cone and the abelian inverse-limit cone are normalized on
complexes. The unit equation specifies the comparison, in addition to its finite projections.
Index `n : ℕ` denotes positive level `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The actual module direct image of the ringed sequence projection: compatible families
of scalar-restricted sections. Source: Stacks 0941, 0D6E
(blueprint: lem-coef-sequence-sections-limit-comparison). -/
def sequenceProjectionDirectImage
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    StrictRingSystem B ⥤ sequenceCoefficientModules A :=
  d.restriction.functor ⋙ lim

/-- Inverse limit is additive, being a finite-product-preserving functor.
Source: Stacks 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceModuleLimitAdditive (A : Sheaf J CommRingCat.{w}) :
    (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ sequenceCoefficientModules A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Abelian inverse limit is additive.
Source: Stacks 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceAbLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the specified projection direct image.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceProjectionDirectImageAdditive
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    (sequenceProjectionDirectImage d).Additive :=
  inferInstanceAs (d.restriction.functor ⋙ lim).Additive

/-- Global sections preserve tower limits, with the usual limit-preservation structure.
Source: Stacks 01FT, 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceSectionsPreservesTowerLimits (A : Sheaf J CommRingCat.{w}) :
    PreservesLimitsOfShape ℕᵒᵖ (sequenceCoefficientSections A) := by
  change PreservesLimitsOfShape ℕᵒᵖ
    (SheafOfModules.forget (derivedChangeRingIndependentCoefficients J A) ⋙
      PresheafOfModules.toPresheaf (derivedChangeRingIndependentCoefficients J A).obj ⋙ lim)
  infer_instance

/-- The ordinary comparison sends a section to its actual family of cone projections.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-sections-limit-comparison). -/
def sequenceSectionsLimitOrdinary
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    sequenceProjectionDirectImage d ⋙ sequenceCoefficientSections A ≅
      (d.restriction.functor ⋙ sequenceTowerSections A) ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) :=
  Functor.isoWhiskerLeft d.restriction.functor
    (preservesLimitNatIso (sequenceCoefficientSections A))

/-- Derived global sections of the total direct image agree canonically with the total
inverse limit of strict derived sections, retaining all actual finite projections.
Source: Stacks 079P, 0941 and 0D6E
(blueprint: lem-coef-sequence-sections-limit-comparison).

Proof plan:
1. Identify strict systems with modules on the sequence site by
   lem-pur-system-ringed-sequence-site. Factor the ringed projection through the constant
   A-ring sequence. The first direct image is exact scalar restriction U
   (def-pc-sheaf-restrict-scalars); the second is lim, with its actual cone.
2. Use prop-pur-kinjective-resolutions-exist to choose strict resolutions J to I,
   U(I) to K, and termwise sections of K to H. Use the same K for the finite comparisons
   of lem-coef-sequence-global-sections-evaluation.
3. By lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lim(U(I)) to lim(K)
   is a quasi-isomorphism. The exact constant-tower left adjoint and
   lem-weil-pbc-right-adjoint-preserves-kinjective make lim(K) K-injective.
   By lem-weil-tower-evaluation-kinjective every K_n is K-injective as well.
4. Global sections of lim(K) identify with lim of termwise sections by the ordinary
   comparison sequenceSectionsLimitOrdinary. It sends each compatible family to itself,
   so its nth projection is sections of the nth cone projection.
5. Apply the normalized composition theorem to termwise sections and the sequence-to-point
   morphism. It makes lim of the resolution into H a quasi-isomorphism. Thus its composite
   with the ordinary comparison gives the required isomorphism into Rlim(G(J)), computed
   as in lem-weil-pbc-ringed-strict-tower-homotopy-limit. The displayed unit equation is
   precisely this common-direct-image normalization.
6. The strict equations pr_K lim(v) = v_n pr_UI and pr_H beta = w_n Gamma(pr_K)
   identify the nth projection with sections of the total-limit projection. Composing
   with the inverse scalar comparison of the sections-evaluation dependency gives the
   finite B_n-sections equation below.
7. The composition and finite comparisons are natural on derived morphisms; their
   normalization makes the construction independent of resolutions. Strict cone equations
   retain every transition after localization. No varying-ring evaluation or scalar
   restriction is asserted to preserve K-injectives. -/
theorem coefficientSequenceSectionsLimitComparison
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (d : SequenceSectionsComparisons B A α) (_hd : d.Normalized) :
    ∃ (P : SequenceSectionsDerivedPair (sequenceProjectionDirectImage d))
      (L : SequenceSectionsDerivedPair
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}))
      (πP : ∀ n : ℕ, P.functor ⟶ d.restriction.functor.mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategory)
      (πL : ∀ n : ℕ, L.functor ⟶
        ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory)
      (κ : P.functor ⋙ (d.finite A).functor ≅ d.global ⋙ L.functor),
      (∀ (X : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ),
        P.unit.app X ≫ (πP n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategory.map
              (d.restriction.functor.mapDerivedCategoryFactors.hom.app X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategoryFactors.hom.app
              ((d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n))
          (.up ℤ)).app ((d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ) (n : ℕ),
        L.unit.app X ≫ (πL n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
            (op n)).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)) ∧
      (∀ X : CochainComplex (StrictRingSystem B) ℤ,
        (d.finite A).unit.app
            (((sequenceProjectionDirectImage d).mapHomologicalComplex (.up ℤ)).obj X) ≫
          (d.finite A).functor.map (P.unit.app X) ≫
          κ.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (sequenceSectionsLimitOrdinary d) (.up ℤ)).hom.app X) ≫
          L.unit.app (((d.restriction.functor ⋙ sequenceTowerSections A).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          L.functor.map (d.tower.unit.app
            ((d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
          L.functor.map (d.tower.functor.map
            (d.restriction.functor.mapDerivedCategoryFactors.inv.app X))) ∧
      (∀ (M : DerivedCategory (StrictRingSystem B)) (n : ℕ),
        κ.hom.app M ≫ (πL n).app (d.global.obj M) ≫ (d.finiteEvaluation n).hom.app M =
          (d.finite A).functor.map ((πP n).app M) ≫
            (d.finite A).functor.map
              ((sequenceRestrictionDerivedEvaluation d.restriction n).hom.app M) ≫
            (d.scalar (α.app (op n))).inv.app ((derivedSystemEvaluation B n).obj M)) := by
  sorry

end SheafOfModules
