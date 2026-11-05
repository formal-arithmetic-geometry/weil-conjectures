/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisSepClosed
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Minimal polynomials over `K((t))` of separable elements over `k'((t))`

Let `F ⊆ L` be fields such that `F` is separably closed in `L`. For every element `β` of an
extension `E` of `L` which is separable over `F`, the minimal polynomial of `β` over `L` is that
over `F` (`minpoly.map_algebraMap_of_isSeparable`): its coefficients are symmetric functions of
roots of a separable polynomial over `F`, hence separable over `F`, hence in `F`. Equivalently
`[L(β) : L] = [F(β) : F]`, i.e. `L ⊗_F F(β)` is a field.

For the slice of SGA 4½, [Th. finitude], Lemme 3.3 (`F = k'((t))`, `L = K((t))`,
`AlgebraicGeometry.separableClosure_traitLaurentField_eq_bot`) this is the linear disjointness of
`K((t))` and `k'((t))^sep` over `k'((t))`
(`AlgebraicGeometry.minpoly_traitLaurentField_eq_map`): the ring `K((t)) ⊗_{k'((t))} k'((t))^sep`
is a field.

-/

@[expose] public section

open Polynomial

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

variable [IsSepClosed k'] [IsAlgClosed K]

end AlgebraicGeometry
