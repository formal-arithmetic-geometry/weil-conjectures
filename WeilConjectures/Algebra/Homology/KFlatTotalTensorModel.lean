/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
/-!
# Flat-term K-flat total tensor models

Source: Stacks Project, Cohomology on Sites, Tags 07A2 and 07A4;
Modules on Sites, Tag 0G6Q (auxiliary; not a blueprint node).

The helpers below only specialize existing category and tensor constructions.
The derived tensor in the conclusion is exactly the localized bifunctor supplied by
`site_derived_tensor_descent_independentCoefficients`, characterized by its natural
representative comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.KFlatTotalTensorModel

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

/-- Use the recorded small-site sheafification in the coefficient universe.
Source: Stacks, Section 03DA (auxiliary; not a blueprint node). -/
instance smallSiteHasSheafify : HasSheafify J AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u, v, r}

/-- Use the recorded locally-bijective criterion in the coefficient universe.
Source: Stacks, Section 03DA (auxiliary; not a blueprint node). -/
instance smallSiteWEqualsLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u, v, r}

end SheafOfModules.KFlatTotalTensorModel
