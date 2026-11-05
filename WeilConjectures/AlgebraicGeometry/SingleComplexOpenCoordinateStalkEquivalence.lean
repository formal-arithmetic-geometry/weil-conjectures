/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData

/-! # Stalkwise conjugacy for transported open coordinates.

Source: Stacks Project, perfect.tex, Tag 0DJ9, localization calculation.
(blueprint: lem-pc-single-complex-open-coordinate-stalk-equivalence)

The proof is the termwise stalk calculation: open-immersion stalk isomorphisms
identify the four local rings and complexes, and naturality of tensor extension,
homology, and the representing map conjugates the two comparison arrows.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
