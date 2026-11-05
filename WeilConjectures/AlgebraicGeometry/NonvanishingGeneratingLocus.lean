/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus

/-! # Nonvanishing and local generation of an invertible module

Source: Stacks Project, Modules, Lemma 01CY, proof at a stalk.
(blueprint: lem-sc-nonvanishing-iff-generates-at).
-/

@[expose] public section

universe u

open CategoryTheory TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry.Scheme.Modules
