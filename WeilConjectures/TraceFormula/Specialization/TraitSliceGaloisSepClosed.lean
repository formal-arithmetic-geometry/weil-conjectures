/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisField

/-!

# `k'((t))` is separably closed in `K((t))`

Let `k'` be a separably closed field and `K` an algebraically closed extension of transcendence
degree `≤ 1`, for instance the field `K = k'(x)^alg` of the generic slices
(`AlgebraicGeometry.traitSliceField`, `AlgebraicGeometry.trdeg_traitSliceField_le_one`). The
coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧` induces an embedding of fraction fields
`F = Frac k'⟦t⟧ ⟶ F_K = Frac K⟦t⟧` (`AlgebraicGeometry.traitLaurentFieldMap`). We prove that
every element of `F_K` separable over `F` lies in `F`
(`AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable`), i.e. the separable closure
of `F` in `F_K` is `F` (`AlgebraicGeometry.separableClosure_traitLaurentField_eq_bot`, and
`AlgebraicGeometry.separableClosure_traitSliceLaurentField_eq_bot` for `K = k'(x)^alg`).

Equivalently, `F_K ⊗_F F^sep` is a field and the restriction of Galois groups
`Gal(F_K^sep / F_K) ⟶ Gal(F^sep / F)` (both are inertia groups, the residue fields being separably
closed) is surjective: this is the surjectivity part of SGA 4½, [Th. finitude], Lemme 3.3, for
the slice `Spec K⟦t⟧ ⟶ 𝔸¹_S`. The proof reduces to the power series statement
`PowerSeries.exists_pow_mem_range_map_of_isRoot`: a simple root in `K⟦t⟧` of a polynomial over
`k'⟦t⟧` is purely inseparable over `k'⟦t⟧`; an element both separable and purely inseparable
over `F` lies in `F`.

-/

@[expose] public section

universe u

open Polynomial

namespace AlgebraicGeometry

section TraitLaurentField

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

variable {k' K} [IsSepClosed k'] [IsAlgClosed K]

end TraitLaurentField

end AlgebraicGeometry
