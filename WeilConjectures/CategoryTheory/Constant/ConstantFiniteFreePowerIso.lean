/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Finite-basis coordinates for constant scalar extension

Source: Stacks 03EK and the finite-dual-basis calculation in step 6 of
`lem-pur-compact-support-roos-cofinality`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC r

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace CategoryTheory

section

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)

variable (n : ℕ)
  (b : ∀ U : Cᵒᵖ,
    @Module.Basis (Fin n) (R.obj.obj U) (S.obj.obj U) _ _
      (Module.compHom _ (α.hom.app U).hom))
  (hb : ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (s : S.obj.obj U) (i : Fin n),
    let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
    letI : Module (R.obj.obj V) (S.obj.obj V) := Module.compHom _ (α.hom.app V).hom
    (b V).equivFun (S.obj.map f s) i =
      R.obj.map f ((b U).equivFun s i))

end

end CategoryTheory
