/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # A common definition of sheafified pure tensor sections

Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: def-sf-common-sheaf-tensor-section).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory
universe c v r
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SheafOfModules

/-- The sheafification image of a sectionwise pure tensor, in independent site sizes.
Source: Stacks 03EK (blueprint: def-sf-common-sheaf-tensor-section). -/
def sheafTensorSection {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r})
    (M N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory R).tensorObj M N).val.obj V :=
  (tensorObjIsoSheafification (R := R) M N).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y))

end SheafOfModules
