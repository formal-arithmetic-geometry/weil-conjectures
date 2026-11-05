/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Localization.HomEquiv

/-! # Supported maps are eventually killed by Koszul augmentations

Source: Stacks Project, Tags 08DC, 08DD and 09IR.
(blueprint: lem-pc-koszul-supported-augmentation-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Obtain augmentation compatibility in the standard localization, then use naturality
-- of the localization comparison to identify the two composites in the chosen category.

end AlgebraicGeometry
