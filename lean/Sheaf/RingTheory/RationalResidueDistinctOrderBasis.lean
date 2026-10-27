/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q134
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Sheaf.RingTheory.DVRValuationRingCharacterization

/-!
# Bases with distinct orders over a rational residue field

Source: Stacks Project, Algebra, Tag 00IE, Definition `definition-value-group`, for the
normalized valuation. The basis theorem is an agent auxiliary, proved by dimension induction,
not an assertion of Tag 00IE (blueprint: lem-sfb-rational-residue-distinct-order-basis).
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- A finite-dimensional subspace of the fraction field of a DVR with scalar residue field
has a basis with strictly increasing normalized orders.

Source: Stacks Project, Algebra, Tag 00IE, Definition `definition-value-group`, for the
valuation convention; Tag 00PD, Lemma `lemma-characterize-dvr`, for the DVR context.
The basis assertion is an agent auxiliary
(blueprint: lem-sfb-rational-residue-distinct-order-basis).

Here `algebraMap R K` identifies `R` with its image in `K`, and the scalar tower says that
this subring contains the given copy of `k`. The residue hypothesis is bijectivity of the
restriction of the quotient homomorphism, hence exactly its being a ring isomorphism.
The additive normalized order on nonzero elements is `-WithZero.log` of the canonical
maximal-ideal valuation. A basis vector is nonzero, so the junk value of `log 0` is unused.

Proof:
1. Induct on `d = Module.finrank k U`, simultaneously for all subspaces of dimension less
   than `d`. For `d = 0`, `U = 0` and the empty basis suffices. For positive `d`, choose a
   finite spanning family `e_i` by `def-weil-finite-dimensional-subspace`. Express each
   `e_i = a_i / b_i` with `a_i, b_i` in `R` and `b_i` nonzero, using the fraction-field
   hypothesis. Their denominator product `q` is nonzero and `q U` is contained in `R`,
   since the scalars lie in `R`.
2. By `lem-sc-dvr-valuation-ring-characterization` and `lem-sc-dvr-valuation-arithmetic`,
   every nonzero `x` in `U` has order at least `-order(q)`. A nonempty bounded-below set
   of integers has a minimum (subtract a lower bound and use the least-natural-number
   principle). Choose a nonzero `u` in `U` of minimal order `n`. Every `x / u` belongs
   to `R` by `lem-sc-dvr-nonnegative-valuation-in-ring`; include `x = 0` separately.
3. Let `rho : R → R/m` be reduction and `iota : k ≃ R/m` its restriction, supplied by
   the residue hypothesis. Set `lambda(x) = iota.symm(rho(x/u))`. Division by `u` is
   additive and `rho(c*x/u) = iota(c)*rho(x/u)`, so `lambda` is `k`-linear, with
   `lambda(u) = 1`. Put `W = ker(lambda)`. For a nonzero `w` in `W`, `w/u` lies in the
   maximal ideal and is not a unit. Its order is nonnegative by minimality and nonzero
   by the quotient definition of the value group. Therefore `order(w) > n`.
4. The vectors `e_i - lambda(e_i)*u` span `W`: apply `lambda` to an expansion of any
   `w` in `W` in the `e_i` to see its coefficients' weighted sum is zero. Thus `W` is
   finite-dimensional. Since `lambda(c*u) = c`, its image is `k`, of dimension one.
   Apply `lem-weil-pbc-idempotent-charpoly-rank-nullity` to get
   `1 + dim(W) = d`, so `dim(W) = d - 1 < d`.
5. The induction hypothesis supplies a basis of `W` of strictly increasing orders, all
   greater than `n`. Prepend `u`. Every `x` decomposes as
   `lambda(x)*u + (x - lambda(x)*u)`, proving spanning. Apply `lambda` to any relation
   to kill its coefficient of `u`; independence of the basis of `W` kills the others.
   This gives the desired `d`-element ordered basis, including the empty tail for `d = 1`.
-/
theorem exists_basis_strictMono_order_of_residue_bijective
    (k : Type u) (K : Type v) (R : Type w)
    [Field k] [Field K] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra k K] [Algebra k R] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K]
    (hres : Function.Bijective ((IsLocalRing.residue R).comp (algebraMap k R)))
    (U : Submodule k K) [FiniteDimensional k U] :
    ∃ b : Module.Basis (Fin (Module.finrank k U)) k U,
      StrictMono (fun i ↦ -WithZero.log ((maximalIdeal R).valuation K (b i : K))) := by
  sorry

end IsDiscreteValuationRing
