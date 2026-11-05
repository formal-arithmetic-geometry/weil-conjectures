/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Nonvanishing loci under restriction along an open immersion

Source: Stacks Project, Properties, Lemma 01PV, the translation to the affine algebra
problem; Modules, Lemma 01CY, the stalk criterion for nonvanishing
(blueprint: lem-sc-nonvanishing-locus-restrict).
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

end AlgebraicGeometry.Scheme.Modules
