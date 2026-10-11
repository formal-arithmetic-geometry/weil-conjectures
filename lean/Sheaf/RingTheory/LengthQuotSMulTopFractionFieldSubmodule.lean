/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.LocalRing.Defs

/-!
# Bounded length for a fraction-field submodule modulo a scalar

Source: Stacks Project, Algebra, Tag 00PE, `lemma-finite-length`
(blueprint: lem-weil-pbc-dim-one-submodule-quotient-finite-length).
-/

universe u v

namespace Submodule

/-- Over a one-dimensional Noetherian local domain, reduction of any submodule of a finite
power of the fraction field modulo a nonzero scalar has bounded finite length.
Source: Stacks Project, Algebra, Tag 00PE, `lemma-finite-length`
(blueprint: lem-weil-pbc-dim-one-submodule-quotient-finite-length).

Proof (the node's nine steps):
1. The nonzero scalar is a nonzerodivisor. Dimension one and Noetherianity give finite length
   of `R/xR` by `lem-weil-pbc-dim-le-one-principal-quotient-finite-length`; write its length as l.
2. If x is a unit, `xM = M`, so the quotient has length zero (`def-weil-pbc-module-length`).
3. Replace the ambient space by the K-span of M, of dimension r' at most r. A basis identifies
   it with `K^r'` and preserves the quotient length (`def-weil-pbc-module-length`). The case
   r' = 0 is immediate. Treat finite M first, then arbitrary M.
4. For finite M, clear denominators by a nonzero scalar, giving an isomorphic module inside
   `F = R^r'`, still spanning `K^r'`; the quotient length is unchanged.
5. Clearing denominators in expressions for the standard basis gives nonzero d with `dF ⊆ M`.
   Every prime containing d is maximal, by dimension one. Thus x is in the radical of dR
   (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`), so `x^c F ⊆ M` for some c.
6. Cancellation of nonzero powers of x identifies each `x^i N/x^(i+1) N` with `N/xN`.
   Additivity (`lem-weil-pbc-length-additive-short-exact`) and induction give
   `length(N/x^n N) = n length(N/xN)`.
7. Coordinatewise reduction identifies `F/xF` with `(R/xR)^r'`. Additivity and induction give
   length r'l, and step 6 gives `length(F/x^n F) = nr'l`.
8. The inclusions `x^(n+c) F ⊆ x^n M ⊆ x^n F` and `x^n M ⊆ M ⊆ F`, together with
   additivity, bound `n length(M/xM)` above by `(n+c)r'l`. First this makes the length finite;
   then let n grow to obtain `length(M/xM) ≤ r'l ≤ rl`.
9. For arbitrary M, choose representatives of the k strict steps of any chain in `M/xM`.
   Their finite span M' gives, by inverse images, a strict chain of k steps in `M'/xM'`.
   The finite case gives `k ≤ rl`. Taking the supremum of all chain lengths gives the bound
   and finite length (`def-weil-pbc-module-length`). -/
theorem length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x R) < ⊤ ∧
      Module.length R (QuotSMulTop x M) < ⊤ ∧
      Module.length R (QuotSMulTop x M) ≤ (r : ℕ∞) * Module.length R (QuotSMulTop x R) := by
  sorry

end Submodule
