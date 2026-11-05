/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso

/-! # K-flatness under open restriction

Source: Stacks Project, Tag 06YB, applied to open restriction.
(blueprint: lem-pc-kflat-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
