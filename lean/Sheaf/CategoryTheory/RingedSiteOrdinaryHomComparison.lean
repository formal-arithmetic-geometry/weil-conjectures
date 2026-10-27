/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U7
-/
module

public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Ordinary-to-derived Hom comparison on a ringed site

The fixed augmentation and localization comparison are shared by shift normalization
and coefficient duality. They do not depend on either compatibility theorem.
Source: Stacks Project, Tags 079P, 0A8X and 0A95
(blueprint: lem-sfb-ringed-site-ordinary-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules WeilConjectures
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]

attribute [local irreducible] homComplexFunctor homComplexπ
  derivedInternalHomOfUniverses

/-- The actual augmentation to the fixed K-injective replacement.
Source: Stacks 079P (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteHomAugmentation : 𝟭 _ ⟶ WeilConjectures.coefficientHomResolution.{r, c, v} J R :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  CochainComplex.toKInjectiveResolution.{max c v r} _

/-- The action of the recorded Hom-complex bifunctor, with both variables explicit.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteHomComplexMap
    {E E' F F' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : E' ⟶ E) (g : F ⟶ F') :
    homComplex.{c, v, max c v r, max c v r} (R := R) E F ⟶
      homComplex.{c, v, max c v r, max c v r} (R := R) E' F' :=
  ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op).app F ≫
    ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E')).map g

/-- Ordinary Hom to derived Hom, using the fixed augmentation and localization factorization.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryHomComparison (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    DerivedCategory.Q.obj (homComplex.{c, v, max c v r, max c v r} (R := R) E F) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map
    (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E) ((ringedSiteHomAugmentation.{c, v, r} J R).app F))
      ≫
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R E F).inv

/-- The ordinary comparison is invertible precisely when its augmentation Hom map is.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: the factorization comparison is an isomorphism. Q inverts the displayed
quasi-isomorphism, so their composite is an isomorphism. -/
theorem ringedSiteOrdinaryHomComparison_isIso (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (h : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :
    IsIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F) := by
  let _ := h
  unfold ringedSiteOrdinaryHomComparison
  infer_instance

/-- The specified comparison iso when ordinary Hom computes derived Hom.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryHomIso (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (h : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :=
  letI := ringedSiteOrdinaryHomComparison_isIso.{c, v, r, w} J R E F h
  asIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F)

end CategoryTheory
