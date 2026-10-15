/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Flat sheaves of modules

Source: Stacks Project, Modules on Sites, Definition 03ER, item (3)
(blueprint: def-pc-flat-sheaf-modules).

The tensor functor is `siteSheafTensorRight`, the sheafification of the sectionwise
balanced tensor product. Unlike the specialized monoidal API, it allows independent
site-object, site-morphism, coefficient and module universes.
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
  `siteSheafTensorRight`)
is exact: it preserves finite limits and finite colimits. The sheafification instance arguments on
  the
site provide the sheafification of presheaves of modules, hence the abelian category `Mod(R)`.
Source: Stacks Project, Tag 03ER, item (3) (blueprint: def-pc-flat-sheaf-modules). -/
def IsFlatOnSite
    (F : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    Prop :=
  exactFunctor _ _ (siteSheafTensorRight F)

end SheafOfModules
