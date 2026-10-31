/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Diagonalizable groups over commutative rings

Source: Conrad, Reductive group schemes, Appendix B.1, printed p.280
(blueprint: def-sfb-ring-diagonalizable-group).

The constructions use the canonical group-algebra Hopf structure and the Hopf-spectrum functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The diagonalizable group Spec R[M] over an arbitrary commutative ring.
The basis e_m has coproduct e_m ⊗ e_m, counit 1 and antipode e_(-m).
Source: Conrad, Reductive group schemes, Appendix B.1, printed p.280
(blueprint: def-sfb-ring-diagonalizable-group). -/
noncomputable abbrev ringDiagonalizableGroup (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] : Grp (Over (Spec (.of R))) :=
  (hopfSpec (.of R)).obj (op (CommHopfAlgCat.of R (AddMonoidAlgebra R M)))

/-- The homomorphism D_R(N) → D_R(M) induced by e_m ↦ e_(α m).
Source: Conrad, Reductive group schemes, Appendix B.1 and Remark B.1.2, printed p.280
(blueprint: def-sfb-ring-diagonalizable-group). -/
noncomputable abbrev ringDiagonalizableGroupMap (R : Type u) [CommRing R]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] (α : M →+ N) :
    ringDiagonalizableGroup R N ⟶ ringDiagonalizableGroup R M :=
  (hopfSpec (.of R)).map (CommHopfAlgCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom R α)).op

end AlgebraicGeometry
