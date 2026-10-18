/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CompletedIntegralCoefficients

/-!
# Intrinsic derived tensor with independent site and coefficient sizes

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU
(blueprint: def-weil-derived-tensor).

This is the same K-flat construction on the actual site, including its localized sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe c v r w t u
open CategoryTheory MonoidalCategory

namespace SheafOfModules

/-- Resolve the canonical representative of the first argument and take total tensor
with the representative of the second. No arbitrary tensor functor is supplied as data.
Source: Stacks Tags 06YS and 06YU (blueprint: def-weil-derived-tensor). -/
def ringedSiteDerivedTensorOfUniverses
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (K L : DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  let K₀ := DerivedCategory.Q.objPreimage K
  let L₀ := DerivedCategory.Q.objPreimage L
  let P := (CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := R) K₀).choose
  letI := SheafOfModules.monoidalCategory R
  DerivedCategory.Q.obj (CochainComplex.mapBifunctor P L₀ (curriedTensor _))

end SheafOfModules
