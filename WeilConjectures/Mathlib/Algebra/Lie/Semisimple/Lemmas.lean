/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Lie algebras with a faithful semisimple representation

A finite-dimensional Lie algebra over an algebraically closed field of characteristic zero
which admits a faithful semisimple finite-dimensional representation is reductive: its radical
is central, and the algebra is the sum of its centre and its derived subalgebra.

Mathlib does not (yet) have a `LieModule.IsSemisimple` class, so "`M` is a semisimple
representation of `L`" is spelled here as `ComplementedLattice (LieSubmodule k L M)`, i.e. the
lattice of Lie submodules of `M` is complemented. This mirrors `IsSemisimpleModule`, which is
by definition `ComplementedLattice (Submodule R M)`.

## Main declarations

* `LieAlgebra.hasCentralRadical_and_center_sup_derivedSeries_eq_top`: a finite-dimensional Lie
  algebra with a faithful semisimple finite-dimensional representation has central radical and
  is the sum of its centre and its derived subalgebra.
-/

@[expose] public section

namespace LieAlgebra

open LieModule

variable (k L M : Type*) [Field k] [CharZero k] [IsAlgClosed k]
  [LieRing L] [LieAlgebra k L] [Module.Finite k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
  [IsFaithful k L M] [ComplementedLattice (LieSubmodule k L M)]

/-- Blueprint `sk-p-lie`: Lie algebra structure. A finite-dimensional Lie algebra `L` over an
algebraically closed field of characteristic zero admitting a faithful semisimple
finite-dimensional representation `M` is reductive: its radical coincides with its centre
`Z(L)`, and `L` is the sum of `Z(L)` and the derived subalgebra `[L, L]`. -/
theorem hasCentralRadical_and_center_sup_derivedSeries_eq_top :
    HasCentralRadical k L ∧ center k L ⊔ derivedSeries k L 1 = ⊤ := by
  sorry

end LieAlgebra
