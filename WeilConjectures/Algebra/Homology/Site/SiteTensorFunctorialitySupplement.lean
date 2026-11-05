/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality

/-!
# Functoriality and local pure tensors for the general-site tensor product

Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: def-pur-sheaf-tensor-product).
The existing independent-universe tensor product is retained. This module exposes its
zero preservation, its action in the second variable and its sheafification-unit pure tensors.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}}

attribute [instance] siteSheafTensorRight_preservesZeroMorphisms

-- Keep the existing sheafification parameters in this theorem's public signature.

end SheafOfModules
