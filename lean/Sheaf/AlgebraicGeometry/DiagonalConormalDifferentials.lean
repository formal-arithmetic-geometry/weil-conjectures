/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.AffineConormalSections

/-!
# Conormal sheaf of the diagonal and relative differentials

Source: Stacks Project, Tag 08S2
(blueprint: lem-sc-smooth-proper-diagonal-conormal-differentials).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{v}}

/-- The conormal module of the diagonal is the sheaf of relative Kähler differentials.
Source: Stacks, Tag 08S2
(blueprint: lem-sc-smooth-proper-diagonal-conormal-differentials).
Proof, step 1: cover X by affine U = Spec A mapping into affine V = Spec R.
The opens U ×_V U form the neighbourhood W of the diagonal from Tag 01KJ.
The diagonal there is cut out by I = ker(A ⊗_R A → A).
By lem-weil-pbc-affine-conormal-sections, conormal sections over U are I/I².
By lem-sc-kahler-differentials-diagonal-ideal, this is Ω_{A/R}, with da
corresponding to the class of 1 ⊗ a - a ⊗ 1 (def-weil-pbc-kahler-differentials).
Step 2: these maps commute with restriction to smaller affine opens because
that formula is unchanged and the da generate. They glue to the canonical
isomorphism; it is an isomorphism because this holds on the affine basis. -/
theorem diagonalConormal_iso_relativeDifferentials (f : X ⟶ S) :
    Nonempty (diagonalConormal f ≅ f.relativeDifferentials) := by
  sorry

end AlgebraicGeometry
