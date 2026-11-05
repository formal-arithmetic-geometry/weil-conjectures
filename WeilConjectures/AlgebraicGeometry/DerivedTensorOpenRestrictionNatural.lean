/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.KFlatBifunctorIsoDescent
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Natural tensor comparison for derived open restriction

Source: Stacks Project, Tag 06YH (derived tensor construction) and Tag 08EU (locality).
(blueprint: lem-pc-derived-tensor-open-restriction-natural).
-/

@[expose] public section

universe u w wO
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace AlgebraicGeometry

-- Compose model comparisons abstractly to avoid unfolding concrete localization functors.

end AlgebraicGeometry
