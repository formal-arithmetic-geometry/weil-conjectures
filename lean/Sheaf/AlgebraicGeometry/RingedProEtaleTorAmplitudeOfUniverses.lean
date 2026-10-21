/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Tor tests on the original site with independent universes

Source: Stacks Project, sites-cohomology.tex, Tag 08FZ
(blueprint: def-weil-proetale-tor-amplitude).
The coefficient-sized small-model predicates remain available. This interface applies
exactly the same degree-zero module tests to the original ringed site and its slices.

## Main definitions

- `HasRingedSiteTorAmplitudeOfUniverses`: the universal degree-zero module test.
- `HasFiniteRingedSiteTorAmplitudeOfUniverses`: existence of one ordered interval.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c h r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Tor amplitude on a ringed site: test the canonical K-flat derived tensor against
all module sheaves in degree zero, with one common ordered interval.
Source: Stacks Project, Tag 08FZ (blueprint: def-weil-proetale-tor-amplitude).
For the pro-etale application R is the constant coefficient ring; on a slice it is
its ordinary restriction, canonically the same constant coefficient ring there. -/
def HasRingedSiteTorAmplitudeOfUniverses {C : Type c} [Category.{h} C]
    [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (K : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (a b : ℤ) : Prop :=
  a ≤ b ∧ ∀ (L : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (q : ℤ), q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients J R).obj
          (K, (DerivedCategory.singleFunctor _ 0).obj L)))

/-- Finite Tor amplitude means one ordered interval works for every module test.
Source: Stacks Project, Tag 08FZ (blueprint: def-weil-proetale-tor-amplitude). -/
def HasFiniteRingedSiteTorAmplitudeOfUniverses {C : Type c} [Category.{h} C]
    [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (K : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) : Prop :=
  ∃ a b : ℤ, HasRingedSiteTorAmplitudeOfUniverses R K a b

end CategoryTheory
