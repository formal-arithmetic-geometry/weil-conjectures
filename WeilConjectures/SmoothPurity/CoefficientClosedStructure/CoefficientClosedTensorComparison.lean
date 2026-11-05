/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # The evaluation-preserving comparison of closed tensor presentations

Source: Stacks 08J9; uniqueness of adjoints applied in both tensor variables.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b
open CategoryTheory Opposite
namespace WeilConjectures.CoefficientClosedStructure
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}

end WeilConjectures.CoefficientClosedStructure
