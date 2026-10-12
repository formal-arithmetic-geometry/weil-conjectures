/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Units on finite locally free modules

Source: Stacks Project, Tags 0BDP and 01E8.
(blueprint: lem-sc-finite-locally-free-tensor-unit)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The tensor-pullback adjunction unit is invertible on finite locally free modules
when it is invertible on the structure module.
Source: Stacks Project, Tag 01E8, degree-zero projection formula and its local proof;
Tag 0BDP, projection-formula paragraph.
(blueprint: lem-sc-finite-locally-free-tensor-unit)

Proof: Cover Y by opens U on which N is free with a finite basis of size r. Direct
image restricts to the full inverse image of U, and tensor pullback along U's inclusion
is restriction. The defining section formula for the chosen adjunction unit is
m ↦ 1 ⊗ m. Both tensor pullback and direct image preserve finite direct sums, so in
these coordinates the unit at N is the direct sum of r copies of the restricted
unit at O_Y. The latter is an isomorphism by hypothesis. Hence the unit at N is
invertible on each U, and inverses glue by uniqueness. For r = 0 the unit is the
identity of the zero object. If Y is empty, the assertion is vacuous locally. -/
theorem isIso_tensorPullback_unit_of_finiteLocallyFree {X Y : Scheme.{u}}
    (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)))
    (N : Y.Modules) [N.IsFiniteLocallyFree] :
    IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app N) := by sorry

end AlgebraicGeometry.Scheme
