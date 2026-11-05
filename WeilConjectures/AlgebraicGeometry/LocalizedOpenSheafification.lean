/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Sheafification and the localized open-site equivalence
Source: Stacks Project, Tag 01CD, localized-site construction.
(blueprint: lem-sc-localized-open-sheafification).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- Every presheaf is a sheaf for the bottom topology. This lets us reuse the proved
module-sheaf transport adjunction to construct its presheaf counterpart. -/

end AlgebraicGeometry
