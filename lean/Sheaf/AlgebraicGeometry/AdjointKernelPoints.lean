/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.Algebra.DualNumber

/-! # The adjoint kernel on algebra-valued points

Source: Milne, Algebraic Groups (2017), 10.20--10.23 and Proposition 14.23, p.285
(blueprint: def-sfb-adjoint-kernel-points).

Conjugation fixes a tangent vector precisely when its dual-number point commutes
with the constant extension of the conjugating point. The reduction condition
selects tangent vectors at the identity over the whole test algebra, including
its nilpotents. For a smooth finite-type group over a field these vectors are
Lie(G) tensor A, so this is exactly the kernel of Ad on A-points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The kernel of differentiated conjugation, on every commutative test algebra.
The maps are the actual dual-number augmentation and constant inclusion. The
condition is identity conjugation on the tangent vectors over A, without any
restriction to field-valued or reduced points.
Source: Milne, 10.20--10.23 and Proposition 14.23, p.285
(blueprint: def-sfb-adjoint-kernel-points). -/
def adjointKernelPoints {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) (A : Type u) [CommRing A] [Algebra k A] :
    Set (StandardGroupSchemes.affine k A ⟶ G.X) :=
  {g | ∀ v : StandardGroupSchemes.affine k (DualNumber A) ⟶ G.X,
    StandardGroupSchemes.map k (TrivSqZeroExt.fstHom k A A) ≫ v = 1 →
      Commute (StandardGroupSchemes.map k (TrivSqZeroExt.inlAlgHom k A A) ≫ g) v}

end AlgebraicGeometry
