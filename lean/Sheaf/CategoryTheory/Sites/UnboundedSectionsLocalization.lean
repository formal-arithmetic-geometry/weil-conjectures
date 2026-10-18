/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal
public import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Unbounded sections and localization of a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0D6F and its K-injective proof
(blueprint: lem-sfb-unbounded-sections-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedSectionsLocalization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The common-universe module category is Grothendieck abelian by the recorded
ring-sheaf theorem. Source: Stacks, Section 07A5
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses J R

/-- Evaluation at an object, followed by forgetting scalars.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev evaluation (W : C) : ringedSiteModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op W) ⋙
    forget₂ (ModuleCat.{u} (R.obj.obj (op W))) AddCommGrpCat.{u}

/-- Restriction is additive by the existing localized adjunction interface.
Source: Stacks, Tags 03DJ and 08FI
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance restrictionAdditive (W : C) : (SheafOfModules.overFunctor.{u} R W).Additive :=
  (Classical.choose_spec
    (localized_restriction_adjunction R W (module_overFunctor_preservesZero R W))).2.2.1

/-- Termwise restriction of an unbounded complex.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev restrictComplex (W : C) :=
  (SheafOfModules.overFunctor.{u} R W).mapHomologicalComplex (.up ℤ)

/-- The restricted complex is K-injective by the recorded Tag 08FI theorem.
Source: Stacks, Tags 08FI and 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance restrictedKInjective (W : C) (I : CochainComplex (ringedSiteModules.{u} R) ℤ)
    [I.IsKInjective] : CochainComplex.IsKInjective ((restrictComplex R W).obj I) :=
  isKInjective_restrict_localized R W inferInstance I

/-- The literal degreewise identity of the two evaluated complexes, including differentials.
Source: Stacks, Tag 0D6F, displayed equality in the proof
(blueprint: lem-sfb-unbounded-sections-localization). -/
def sectionComplexIdentity (W : C) (I : CochainComplex (ringedSiteModules.{u} R) ℤ) :
    ((evaluation R W).mapHomologicalComplex (.up ℤ)).obj I ≅
      ((evaluation (R.over W) (Over.mk (𝟙 W))).mapHomologicalComplex (.up ℤ)).obj
        ((restrictComplex R W).obj I) :=
  Iso.refl _

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{u}]

/-- Unbounded derived evaluation, with scalars forgotten after evaluation.
Source: Stacks, Section 07A5 and Tag 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedEvaluation (W : C) :
    DerivedCategory (ringedSiteModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (evaluation R W).rightDerivedFunctor

/-- Unbounded derived restriction. Since sectionwise restriction is exact, its total
right derived functor is the usual termwise restriction on the derived category.
Source: Stacks, Tags 03DJ, 08FI and 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedRestriction (W : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (R.over W))] :
    DerivedCategory (ringedSiteModules.{u} R) ⥤
      DerivedCategory (ringedSiteModules.{u} (R.over W)) :=
  (SheafOfModules.overFunctor.{u} R W).rightDerivedFunctor

/-- Derived evaluation agrees naturally with derived evaluation on the localized site.
The comparison is normalized on every K-injective representative by the literal identity
of section complexes; its cohomology is an isomorphism in every integer degree.

Source: Stacks Project, Tag 0D6F
(blueprint: lem-sfb-unbounded-sections-localization).

Proof: (1) The site and its slice are small in the common universe. Apply
prop-pur-kinjective-resolutions-exist (Section 07A5, Theorem 079P) to compute the total
right derived functors of sk-def-sfb-derived-categories on K-injective resolutions.
Restriction preserves K-injectives by lem-pur-kinjective-restrict-localized (08FI).
(2) By def-pur-localized-ringed-site, evaluating a restricted complex at id_W gives
exactly I(W), with the same differentials, hence sectionComplexIdentity is degreewise
identity. (3) This identity commutes with chain maps. By
lem-weil-pbc-kinjective-hom-derived, derived morphisms between K-injective representatives
are homotopy classes of chain maps, so the identity descends independently of the chosen
representative and naturally in K. Apply the cohomology functor in any integer degree
to obtain the last clause. No truncation or boundedness is used. -/
theorem unboundedSectionsLocalization (W : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (R.over W))] :
    ∃ e : derivedEvaluation R W ≅
        derivedRestriction R W ⋙ derivedEvaluation (R.over W) (Over.mk (𝟙 W)),
      (∀ (I : CochainComplex (ringedSiteModules.{u} R) ℤ) [I.IsKInjective],
        e.hom.app (DerivedCategory.Q.obj I) ≫
          (derivedEvaluation (R.over W) (Over.mk (𝟙 W))).map
            ((SheafOfModules.overFunctor.{u} R W).rightDerivedFunctorObjQIso I).hom ≫
          ((evaluation (R.over W) (Over.mk (𝟙 W))).rightDerivedFunctorObjQIso
            ((restrictComplex R W).obj I)).hom =
        ((evaluation R W).rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map (sectionComplexIdentity R W I).hom) ∧
      (∀ (K : DerivedCategory (ringedSiteModules.{u} R)) (q : ℤ),
        Nonempty
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
              ((derivedEvaluation R W).obj K) ≅
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
              ((derivedEvaluation (R.over W) (Over.mk (𝟙 W))).obj
                ((derivedRestriction R W).obj K)))) := by
  sorry

end CategoryTheory.UnboundedSectionsLocalization
