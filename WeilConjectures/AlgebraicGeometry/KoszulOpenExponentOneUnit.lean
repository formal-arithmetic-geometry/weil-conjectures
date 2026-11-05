/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSectionsUnit
import WeilConjectures.AlgebraicGeometry.KoszulOpenAugmentationCechUnit
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainClassNaturality

/-! # The augmented exponent-one class is restriction of one

Source: Stacks Project, Tags 08D1 and 08DC.
(blueprint: lem-sc-koszul-open-exponent-one-unit).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
