/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsExtensionUnitNormalization
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization

/-! # Localization of the ordinary affine chart comparison in independent universes
Source: Stacks Project, Tags 06Z0, 08DW(2), 0AA7 and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-chart-model-factorization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
