/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Tensor products and restriction to a localized ringed site

Source: Stacks Project, Modules on Sites, Tags 03EL and 03DH
(blueprint: lem-sfb-localized-site-tensor-restriction).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory Opposite Functor

namespace SheafOfModules

section SheafificationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{m}]
  (R : Sheaf J RingCat.{r}) (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]

end SheafificationComparison

section TensorComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}} (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]

end TensorComparison

attribute [local instance] tensorOverComparison_isIso

end SheafOfModules
