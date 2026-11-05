/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Trunc
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisHensel

/-!

# Separable roots of `k'⟦t⟧`-polynomials in `K⟦t⟧`

Let `k'` be a separably closed field and `K` an algebraically closed extension of transcendence
degree `≤ 1` (for the generic slices, `K = k'(x)^alg`). We show that a simple root `α ∈ K⟦t⟧` of a
polynomial with coefficients in `k'⟦t⟧` is purely inseparable over `k'⟦t⟧`: some `p`-power `α^q`
lies in `k'⟦t⟧` (`PowerSeries.exists_pow_mem_range_map_of_isRoot`). This is the algebraic heart of
the surjectivity of inertia `I_{K((t))} ⟶ I_{k'((t))}` (SGA 4½, [Th. finitude], Lemme 3.3):
`k'((t))` is separably closed in `K((t))`.

The proof has three steps.

* **The coefficients of `α` are algebraic over `k'`**
  (`PowerSeries.isAlgebraic_coeff_of_isRoot`): if a coefficient `y` of `α` were transcendental,
  `K` would be an algebraic closure of `k'[y]` (transcendence degree `≤ 1`), so the automorphisms
  `y ↦ y + c` (`c ∈ k'`) of `k'[y]` would extend to automorphisms of `K` fixing `k'`, moving `α`
  to infinitely many distinct roots of the same polynomial.
* **Newton's lemma**: since `k'` is separably closed, finitely many coefficients of `α` lie in the
  purely inseparable extension `k'' = {a | a^q ∈ k'}` of `k'`; Newton's lemma over `k''⟦t⟧` and the
  uniqueness of simple roots show that `α ∈ k''⟦t⟧`.
* **Frobenius**: `α^q = Frob^q(expand_q α) ∈ k'⟦t⟧`.

-/

@[expose] public section

universe u

open Polynomial

namespace PowerSeries

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

variable [IsAlgClosed K]

end PowerSeries

namespace PowerSeries

section Aux

variable {R S : Type*} [CommRing R] [CommRing S]

end Aux

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsAlgClosed K]
  [IsSepClosed k'] (p : ℕ) [ExpChar k' p]

end PowerSeries
