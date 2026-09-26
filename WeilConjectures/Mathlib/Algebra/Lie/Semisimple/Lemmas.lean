/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Lemmas

/-!
# Lie algebras with a faithful semisimple representation

A finite-dimensional Lie algebra over a field of characteristic zero which admits a faithful
semisimple finite-dimensional representation is *reductive*: its radical is central, and the
algebra is the sum of its centre and its derived subalgebra.

Mathlib does not (yet) have a `LieModule.IsSemisimple` class, so "`M` is a semisimple
representation of `L`" is spelled here as `ComplementedLattice (LieSubmodule k L M)`, i.e. the
lattice of Lie submodules of `M` is complemented; `LieModule.IsSemisimple` below is an `abbrev`
for that. This mirrors `IsSemisimpleModule`, which is by definition
`ComplementedLattice (Submodule R M)`.

The two halves are stated separately, and each under the hypotheses it needs. Centrality of the
radical matches Mathlib's irreducible case
`LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`, including its
`[LieModule.IsTriangularizable k L M]` hypothesis; like that lemma it cannot be an instance,
because the representation `M` does not appear in the conclusion. The reductive decomposition
`L = Z(L) + [L, L]` needs no module at all: it holds for every finite-dimensional
characteristic-zero Lie algebra with central radical.

## Main declarations

* `LieModule.IsSemisimple`: `M` is a semisimple representation of `L`.
* `LieAlgebra.hasCentralRadical_of_isFaithful`: a finite-dimensional Lie algebra with a faithful
  semisimple finite-dimensional representation has central radical.
* `LieAlgebra.center_sup_derivedSeries_eq_top`: a finite-dimensional characteristic-zero Lie
  algebra with central radical is the sum of its centre and its derived subalgebra.

## Blueprint

`LieAlgebra.hasCentralRadical_of_isFaithful` and `LieAlgebra.center_sup_derivedSeries_eq_top`
implement `sk-p-lie`.
-/

@[expose] public section

open LieModule

namespace LieModule

/-- A Lie module `M` over `L` is *semisimple* when its lattice of Lie submodules is
complemented, i.e. every Lie submodule has a complement. -/
abbrev IsSemisimple (k L M : Type*) [CommRing k] [LieRing L] [LieAlgebra k L] [AddCommGroup M]
    [Module k M] [LieRingModule L M] [LieModule k L M] : Prop :=
  ComplementedLattice (LieSubmodule k L M)

end LieModule

namespace LieAlgebra

/-- A finite-dimensional Lie algebra over a field of characteristic zero admitting a faithful
semisimple finite-dimensional representation `M` has central radical.
(blueprint: `sk-p-lie`) -/
theorem hasCentralRadical_of_isFaithful (k L M : Type*) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
    [IsFaithful k L M] [IsTriangularizable k L M] [LieModule.IsSemisimple k L M] :
    HasCentralRadical k L := by
  sorry

/-- A finite-dimensional Lie algebra over a field of characteristic zero whose radical is central
is *reductive*: it is the sum of its centre `Z(L)` and its derived subalgebra `[L, L]`.
(blueprint: `sk-p-lie`) -/
theorem center_sup_derivedSeries_eq_top (k L : Type*) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L] [HasCentralRadical k L] :
    center k L ⊔ derivedSeries k L 1 = ⊤ := by
  sorry

end LieAlgebra
