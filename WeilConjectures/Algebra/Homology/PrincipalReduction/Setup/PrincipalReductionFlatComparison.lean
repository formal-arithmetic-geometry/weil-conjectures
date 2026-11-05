/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.DerivedReductionResolutionIndependence
import all WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.DerivedReductionResolutionIndependence
import WeilConjectures.Algebra.Homology.PrincipalQuotient.PrincipalQuotientQuasiIso
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex

/-! # Invertibility of the flat-resolution comparison

The ordinary principal-quotient counit is invertible on complexes with regular terms,
and exact sections of flat sheaves have regular terms.
(blueprint: lem-pod-principal-reduction-flat-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
universe u v r wO wS wR wA
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace SheafOfModules.PrincipalReduction.Setup
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)

variable [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

end SheafOfModules.PrincipalReduction.Setup
