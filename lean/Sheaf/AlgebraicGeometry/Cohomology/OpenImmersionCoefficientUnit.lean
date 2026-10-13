/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition
/-! # Underlying abelian sheaves under open module pullback

Source: Stacks Project, Tag 04J0 and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {X Y : Scheme.{u}}
/-- The coefficient unit is invertible for an open immersion.
Source: Stacks Project, Tag 04J0, localization of ringed sites, and Section 01F7.
(blueprint: lem-pc-open-coefficient-unit-iso)

Proof: For an open immersion j, inverse image of abelian sheaves is restriction
on opens. The inverse image of the structure sheaf is the structure sheaf,
so module pullback is also restriction. Use the abelian restriction comparison
and restrictFunctorIsoPullback for modules. The module pullback unit is the
restriction unit followed by that comparison. Taking abelian adjoints, its
coefficient morphism is the composite of these two isomorphisms. Thus it is
invertible. The argument covers empty and identity open immersions and the
zero module without any flatness assumption.
-/
theorem coefficientUnit_isIso_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) : IsIso (coefficientUnit j M) := by sorry
end AlgebraicGeometry.Scheme.Modules
