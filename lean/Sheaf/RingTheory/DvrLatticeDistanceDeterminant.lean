/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# Relative length of DVR lattices and the determinant

Source: Stacks Project, Algebra, Tags 02MF, 02MG and 02MI
(`lemma-compare-lattices`, `definition-distance`, `lemma-order-vanishing-determinant`),
specialized to a DVR (blueprint: lem-exc-dvr-lattice-distance-determinant).
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- The signed relative length of a lattice and its image is the determinant valuation.
Source: Stacks Project, Algebra, Tags 02MF, 02MG and 02MI
(blueprint: lem-exc-dvr-lattice-distance-determinant).

The submodule `(M.map (g.toLinearMap.restrictScalars R)).comap M.subtype` is the
intersection `H = M ∩ g(M)` viewed inside `M`; the other `comap` views it inside `g(M)`.
The two lengths are finite, so `ENat.toNat` followed by the cast to `ℤ` retains their values.
The normalized valuation is `WithZero.log (Ring.ordFrac R x)`: by Tag 02MD and
`Ring.ordFrac_irreducible`, it takes a uniformizer to `1` and an R-unit to `0`.

Proof, following the nine steps of the node (the DVR case of Tag 02MI):

1. The submodule `M` is torsion-free: multiplication by a nonzero element of `R` can be
   cancelled in `V` using its inverse in `K`. By `lem-sc-dvr-fg-torsionfree-free`, choose
   a finite R-basis `b` of `M`. It is a K-basis of `V`: full span gives spanning, and
   clearing denominators reduces linear independence to that over `R`. Its image `g(b)`
   is likewise a basis of `g(M)`. If the basis is empty, both quotient lengths are zero
   (`def-weil-pbc-module-length`) and the empty determinant is one
   (`def-weil-pbc-matrix-determinant`, `def-weil-endomorphism-determinant`).
2. Choose a uniformizer `t` (`def-sc-discrete-valuation-ring`). The PID is Noetherian
   (`lem-weil-pbc-pid-noetherian-normal`), so apply
   `lem-weil-pbc-dvr-unit-times-uniformizer-power` to numerator and denominator: each
   nonzero fraction is `u t^r`. The exponent is unique, since otherwise a positive power
   of the nonunit `t` would be a unit. Exponents add under multiplication and negate
   under inversion. Also `t^q x` lies in `R` when `q ≥ 0` and `q + v_R(x) ≥ 0`.
3. The ideals containing `t^s R`, for `s ≥ 0`, are exactly `t^j R` with `0 ≤ j ≤ s`:
   principality and unit-times-power give these ideals, and cancellation gives the
   containment criterion. Quotient inverse image identifies them with the submodules
   of `R / t^s R`, giving length `s` (`def-weil-pbc-module-length`). Thus `R / aR`
   has length `s` for `a = u t^s`. Image and inverse image also show that linear
   isomorphisms preserve lengths.
4. Express each vector of `b` in the K-basis `g(b)`. Choose `q ≥ 0` large enough to
   clear the valuations of all nonzero coefficients. Then `N = t^q M` lies in
   `H = M ∩ g(M)`, has basis `t^q b`, and spans `V`.
5. For either `E = M` or `E = g(M)`, apply
   `lem-sc-dvr-saturation-line-smith-normal-form` to `N ⊆ E`. The Smith bases satisfy
   `f'_i = a_i e'_i` with all `a_i ≠ 0`. Clearing denominators proves their K-linear
   independence. Since `N` spans `V`, no basis vector of `E` is omitted, so the two
   ranks agree. Write `a_i = u_i t^s_i` with `s_i ≥ 0`.
6. The coordinate map from `E` to the finite sum of `R / a_i R` is surjective with
   kernel `N`, hence identifies `E/N` with that sum. Each summand has length `s_i`
   by step 3. Repeatedly apply `lem-weil-pbc-length-additive-short-exact` to insertion
   and projection of the last coordinate. Thus `E/N` has finite length `∑ s_i`.
7. Let `A` be the inclusion matrix of a basis `f` of `N` in a basis `e` of `E`.
   Write `e' = eP` and `f' = fQ`; then `PD = AQ` for `D = diag(a_i)`. The square
   case of `lem-weil-pbc-cauchy-binet` gives determinant multiplicativity, while
   `def-weil-pbc-matrix-determinant` gives the diagonal and identity determinants and
   compatibility with `R → K`. Applying these to the inverse matrices makes `det P`
   and `det Q` units. Taking valuations of `det A det Q = det P ∏ a_i` therefore gives
   `v_R(det A) = ∑ s_i = length_R(E/N)`.
8. Let `G` represent `g` in `b`, and use `t^q b` for both inclusions of `N`. Its matrix
   in `b` is `t^q I`; its matrix `A_g` in `g(b)` satisfies `G A_g = t^q I`.
   The determinant formulas and `def-weil-endomorphism-determinant` give finite
   lengths `length_R(M/N) = qn` and `length_R(g(M)/N) = qn - v_R(det_K(g))`.
   Subtraction in the integers gives the claimed valuation for this common sublattice.
9. The quotient maps give exact sequences with left term `H/N`, middle terms `M/N`
   and `g(M)/N`, and right terms `M/H` and `g(M)/H`. By
   `lem-weil-pbc-length-additive-short-exact` and step 8 all these modules have finite
   length. Subtract the two length equalities in the integers and cancel the common
   `length_R(H/N)` to obtain the result (Tags 02MF and 02MG).
-/
theorem lattice_distance_determinant
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (V : Type w) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [FiniteDimensional K V] (M : Submodule R V) [Module.Finite R M]
    (hspan : Submodule.span K (M : Set V) = ⊤) (g : V ≃ₗ[K] V) :
    Module.length R
        (M ⧸ (M.map (g.toLinearMap.restrictScalars R)).comap M.subtype) ≠ ⊤ ∧
      Module.length R
        (M.map (g.toLinearMap.restrictScalars R) ⧸
          M.comap (M.map (g.toLinearMap.restrictScalars R)).subtype) ≠ ⊤ ∧
      ((Module.length R
          (M ⧸ (M.map (g.toLinearMap.restrictScalars R)).comap M.subtype)).toNat : ℤ) -
        ((Module.length R
          (M.map (g.toLinearMap.restrictScalars R) ⧸
            M.comap (M.map (g.toLinearMap.restrictScalars R)).subtype)).toNat : ℤ) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g.toLinearMap)) := by
  sorry

end IsDiscreteValuationRing
