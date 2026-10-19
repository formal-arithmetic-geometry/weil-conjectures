/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Sheaf.CategoryTheory.LocalCoefficientLocalization
public import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
public import Sheaf.CategoryTheory.RingedSectionLocalizationRing
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.SliceSiteLocalization
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful


/-!
# Derived slice comparisons and pullback of section localization

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-derived-slice-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u w v x

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- The recorded derived restriction with its coefficient presentation fixed explicitly.
Source: Stacks Tags 03DJ and 08JB
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceRestriction {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (A : Sheaf T CommRingCat.{u}) (W : E)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose T (forget₂ CommRingCat RingCat)).obj A).over W))] :
    ringedSiteDerived A ⥤ ringedSiteDerived (A.over W) :=
  CategoryTheory.ringedSliceDerivedRestriction.{u, u, u, w, w} T A W

/-- Restriction of Q of a complex is Q of its actual termwise restriction.
Source: Stacks Tags 03DJ and 08JB
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceRestrictionFactors {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (A : Sheaf T CommRingCat.{u}) (W : E)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose T (forget₂ CommRingCat RingCat)).obj A).over W))] :
    DerivedCategory.Q.{w} ⋙ ringedSliceRestriction.{u, w} A W ≅
      CategoryTheory.ringedSliceComplexRestriction.{u, u, u} T A W ⋙
        DerivedCategory.Q.{w} (C := SheafOfModules.{u}
          ((sheafCompose (T.over W) (forget₂ CommRingCat RingCat)).obj (A.over W))) :=
  CategoryTheory.ringedSliceLocalizationIso.{u, u, u, w, w} T A W

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)

/-- The existing module direct image, with a fixed head for instance inference.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceModulePushforward := pushforward.{u} (ringedSiteModuleMap u a)

/-- The existing module pullback, with a fixed head for instance inference.
Source: Stacks Tag 03D7 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceModulePullback := pullback.{u} (ringedSiteModuleMap u a)

/-- The actual adjunction of these existing functors.
Source: Stacks Tag 03D7 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceModuleAdjunction :
    ringedSliceModulePullback u a ⊣ ringedSliceModulePushforward u a :=
  pullbackPushforwardAdjunction (ringedSiteModuleMap u a)

/-- Direct image is additive because its maps are the original maps on sections.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
instance ringedSlicePushforwardAdditive : (ringedSliceModulePushforward u a).Additive where
  map_add := rfl

/-- The canonical module pullback inherits additivity from its right adjoint.
Source: Stacks Tag 03D7 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
instance ringedSlicePullbackAdditive : (ringedSliceModulePullback u a).Additive :=
  (ringedSliceModuleAdjunction u a).left_adjoint_additive

/-- A presentation of the canonical derived adjunction, retaining both universal
transformations and their normalization under the original module adjunction.
This is data to be produced by the theorem, not an extra assumption on the morphism.
Source: Stacks Tags 06YY, 07A6 and 09T5
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
structure RingedSliceDerivedImage
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))] where
  left : ringedSiteDerived.{u, w} R ⥤ ringedSiteDerived.{u, w} S
  right : ringedSiteDerived.{u, w} S ⥤ ringedSiteDerived.{u, w} R
  epsilon : DerivedCategory.Q.{w} ⋙ left ⟶
    (ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w}
  eta : (ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ right
  isLeftDerived : left.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso _ (.up ℤ))
  isRightDerived : right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso _ (.up ℤ))
  adjunction : left ⊣ right
  normalized : ∀ (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ)
    (h : ((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj I)
      (epsilon.app P ≫ DerivedCategory.Q.{w}.map h) =
      DerivedCategory.Q.{w}.map
        (((ringedSliceModuleAdjunction u a).mapHomologicalComplex
          (.up ℤ)).homEquiv P I h) ≫ eta.app I

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

/-- Ordinary direct image and slice restriction are literally the same complex.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSlicePushforwardComplexIso (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ) :
    (CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj
      (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≅
    ((ringedSliceModulePushforward (Over.post (X := V) u)
        (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).obj
      ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I) :=
  Iso.refl _

/-- The image of the unit generator in the localized target coefficient sheaf.
It is pullback of the ring followed by the actual localization unit, in degree zero.
Source: Stacks Tag 099J (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceLocalizationGenerator
    (t : (S.obj ⋙ CategoryTheory.forget CommRingCat).sections) :
    ((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj
          (unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))) ⟶
      (CochainComplex.singleFunctor _ 0).obj (ringedSectionLocalization S t) :=
  ((HomologicalComplex.singleMapHomologicalComplex
      (ringedSliceModulePullback u a) (.up ℤ) 0).app _).hom ≫
    (CochainComplex.singleFunctor _ 0).map
      (pullbackObjUnitToUnit (ringedSiteModuleMap u a) ≫ ringedSectionLocalizationUnit S t)

/-- The two natural slice comparisons with their unit and counit coherence equations.
These fields bundle precisely the compatibility clauses of the node, with no further
condition on either adjunction or restriction functor.
Source: Stacks Tags 04J0 and 07A6
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
structure RingedSliceAdjunctionSquare
    {A B C D : Type v} [Category.{x} A] [Category.{x} B]
    [Category.{x} C] [Category.{x} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (jA : A ⥤ C) (jB : B ⥤ D) where
  /-- Restriction commutes with the right adjoints. -/
  beta : R ⋙ jA ≅ jB ⋙ R'
  /-- Restriction commutes with the left adjoints, in the inverse orientation. -/
  lambda : jA ⋙ L' ≅ L ⋙ jB
  /-- The counit square. -/
  counit : ∀ M : B,
    L'.map (beta.hom.app M) ≫ adj'.counit.app (jB.obj M) =
      lambda.hom.app (R.obj M) ≫ jB.map (adj.counit.app M)
  /-- The unit square. -/
  unit : ∀ N : A,
    jA.map (adj.unit.app N) ≫ beta.hom.app (L.obj N) ≫ R'.map (lambda.inv.app N) =
      adj'.unit.app (jA.obj N)

set_option backward.isDefEq.respectTransparency.types false in
-- The normalization includes both universal transformations and the adjunction equations.
/-- Canonical derived slice comparisons, their adjunction coherence, and the normalized
pullback of every section localization, for unbounded complexes and arbitrary ring maps.
Source: Stacks Tags 099J, 04J0 and 07A6
(blueprint: lem-weil-pbc-ringed-derived-slice-localization).

Proof:
1. Localize the ringed-site morphism by lem-weil-pbc-localize-ringed-site-morphism.
The two module restrictions are exact (lem-pur-site-restriction-module-adjunction-exact),
so they descend termwise to the unbounded derived categories.
2. Choose a flat-term K-flat resolution by lem-pc-kflat-resolution. Restriction is
pullback along a localization morphism of topoi (lem-weil-pbc-slice-site-localization),
hence remains flat K-flat by lem-weil-pbc-ringed-topos-kflat-pullback and the tensor unit.
The ordinary pullback square computes the two derived pullbacks on this resolution.
3. Descend its naturality through the localization of flat K-flat representatives
(lem-weil-pbc-site-derived-tensor-descent and the localization universal property).
4. Choose a K-injective resolution (prop-pur-kinjective-resolutions-exist); its
restriction is K-injective (lem-pur-kinjective-restrict-localized). The ordinary
identity on sections computes the two derived direct images and the displayed
right-derived normalization. Maps into K-injectives are homotopy classes, proving
naturality and independence (lem-weil-pbc-kinjective-hom-derived).
5. Ordinary inverse adjuncts commute with the square: on r tensor x both paths give
r times h(x). This respects restriction, tensor relations and sheafification.
6. Represent an arbitrary derived arrow by a fraction with flat K-flat denominator
and K-injective target. Apply lem-pc-pre-derived-adjoint-functors-general: on the
injective side the unique maps to the chosen resolution give an essentially constant
ind-diagram; on the flat side the invertible comparison at a flat K-flat stage,
cofilteredness and another flat resolution give an essentially constant pro-diagram.
7. Restrict that fraction; the same computation gives equality of inverse adjuncts
using the ordinary identity in step 5. Both sides are independent of the fraction.
8. Specialize to the identity and to the unit. The triangle identities give exactly
the counit and unit equations stated below (lem-weil-pbc-ringed-projection-mate-exact).
9. R[1/t] is the sheafification of colim(R --t--> R --t--> ...). The n-th stage
sends x to x/t^n; equality of fractions is equality at a later stage, also for zero
divisors (lem-weil-pbc-module-sheaves-colimits-forgetful).
10. Pullback preserves this colimit as a left adjoint; it takes R to S and t to its
structural image. The colimit identification therefore takes the localization unit
to the localization unit. This is the generator equation below.
11. Localization is flat sectionwise (lem-weil-pbc-localization-flat); exact module
sheafification and its tensor comparison imply flatness as a module sheaf. Its
single complex is K-flat (lem-pc-bounded-above-flat-kflat-site), so the ordinary
calculation computes the derived pullback. A section on V need not extend globally. -/
theorem ringedDerivedSliceLocalization
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))] :
    ∃ hc : (Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V)),
      ∃ (e : RingedSliceDerivedImage.{u, w} u a)
        (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
          (localizedRingedSiteMap u a V)),
        ∃ d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
            (ringedSliceRestriction.{u, w} R V)
            (ringedSliceRestriction.{u, w} S (u.obj V)),
          (∀ (I : CochainComplex (SheafOfModules.{u}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
            (ringedSliceRestriction.{u, w} R V).map
                (X := DerivedCategory.Q.{w}.obj
                  (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I))
                (Y := e.right.obj (DerivedCategory.Q.{w}.obj I)) (e.eta.app I) ≫
              d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
              l.right.map
                (X := (ringedSliceRestriction.{u, w} S (u.obj V)).obj (DerivedCategory.Q.{w}.obj I))
                (Y := DerivedCategory.Q.{w}.obj
                  ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
                ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
            (ringedSliceRestrictionFactors.{u, w} R V).hom.app
              (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
              DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
              l.eta.app
                ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I)) ∧
          ∀ t : R.obj.obj (op V),
            ∃ loc : l.left.obj
                ((CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (ringedSectionLocalization (R.over V) (ringedSliceSection R V t))) ≅
                (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (ringedSectionLocalization (S.over (u.obj V))
                    (ringedSliceSection S (u.obj V) (a.hom.app (op V) t))),
              l.left.map
                (X := (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (unit ((sheafCompose (K.over V) (forget₂ CommRingCat RingCat)).obj
                    (R.over V))))
                (Y := (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (ringedSectionLocalization (R.over V) (ringedSliceSection R V t)))
                ((CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).map
                  (ringedSectionLocalizationUnit (R.over V) (ringedSliceSection R V t))) ≫
                  loc.hom =
                l.epsilon.app ((CochainComplex.singleFunctor _ 0).obj
                    (unit ((sheafCompose (K.over V) (forget₂ CommRingCat RingCat)).obj
                      (R.over V)))) ≫
                  DerivedCategory.Q.{w}.map
                    (ringedSliceLocalizationGenerator (Over.post (X := V) u)
                      (localizedRingedSiteMap u a V)
                      (ringedSliceSection S (u.obj V) (a.hom.app (op V) t))) := by
  sorry

end SheafOfModules
