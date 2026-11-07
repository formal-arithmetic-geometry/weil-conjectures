/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat

import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Flat sheaves of modules with independent universes

Source: Stacks Project, Modules on Sites, Definition 03ER, item (3)
(auxiliary; not a blueprint node).

The blueprint node `def-pc-flat-sheaf-modules` is `SheafOfModules.IsFlat`, which needs the
site and the coefficients in one universe. `SheafOfModules.IsFlatOnSite` is the same notion
for independent site-object, site-morphism, coefficient and module universes. Its tensor
functor is `siteSheafTensorRight`, the sheafification of the sectionwise balanced tensor
product. When the universes agree, the two predicates are equivalent
(`SheafOfModules.isFlatOnSite_iff_isFlat`).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory MonoidalCategory

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {R : Sheaf J CommRingCat.{r}}

/-- A sheaf of modules `F` over a sheaf of commutative rings `R` is *flat* when the functor
`G ↦ G ⊗_R F` on sheaves of `R`-modules (the sheafified sectionwise tensor product
`siteSheafTensorRight`) is exact: it preserves finite limits and finite colimits. The
sheafification instance arguments on the site provide the sheafification of presheaves of
modules, hence the abelian category `Mod(R)`. This is `SheafOfModules.IsFlat` with independent
universes, see `SheafOfModules.isFlatOnSite_iff_isFlat`.
Source: Stacks Project, Tag 03ER, item (3) (auxiliary; not a blueprint node). -/
def IsFlatOnSite
    (F : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    Prop :=
  exactFunctor _ _ (siteSheafTensorRight F)

end SheafOfModules

namespace SheafOfModules


end SheafOfModules
