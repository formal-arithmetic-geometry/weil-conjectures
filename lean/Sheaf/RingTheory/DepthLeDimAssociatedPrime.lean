/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Sheaf.RingTheory.AssociatedPrimePowerQuotient
import Sheaf.RingTheory.DepthQuotSMulTop
import Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated

/-!
# Depth is bounded by the dimension at an associated prime

Source: Stacks Project, Algebra, Lemma Tag 0BK4 (lemma-depth-dim-associated-primes),
lines 17985-18020; associated primes Definition Tag 00LA (blueprint:
lem-weil-pbc-depth-le-dim-associated-prime).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- For a finite module over a Noetherian local ring, the depth is at most the
Krull dimension of the quotient by every associated prime. Since `R` is Noetherian,
Mathlib's `associatedPrimes R M` are exactly the primes `p = Ann_R(z)` for some `z : M`
(`isAssociatedPrime_iff`), the node's notion (Stacks 00LA). Source: Stacks Project,
Algebra, Tag 0BK4 (blueprint: lem-weil-pbc-depth-le-dim-associated-prime).

Proof, following the seven steps of the node and Stacks Tag 0BK4:
1. A prime annihilator forces a nonzero element and hence a nonzero module. By
   `lem-weil-pbc-nakayama-jacobson`, the maximal ideal does not generate the whole
   module. Thus `def-weil-pbc-depth` computes depth by regular-sequence lengths.
2. If the maximal ideal is associated, its annihilated nonzero element prevents
   any positive-length regular sequence. The empty sequence gives depth zero.
   Every prime quotient is nonzero, so its dimension is at least zero.
3. Otherwise `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated` supplies a
   nonzerodivisor in the maximal ideal. `lem-weil-pbc-depth-drops-by-one` makes
   depth a finite positive integer. Induct on this integer, starting at zero.
4. Choose such a nonzerodivisor `x`. By
   `lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`, it lies
   outside the associated prime `p`.
5. The local Noetherian domain `R/p` has finite dimension by
   `lem-weil-pbc-noetherian-local-finite-krull-dimension`. Apply
   `lem-weil-pbc-dimension-quotient-nonzerodivisor` to the nonzero image of `x`:
   `A = R/(p + (x))` has dimension one less than `R/p` and is nonzero.
6. Take a maximal-length prime chain of `A`. By
   `lem-weil-pbc-prime-contains-minimal-prime`, choose a minimal prime below its
   first term. Replacing that term gives a chain of the same length in the
   quotient by this minimal prime. Quotient prime correspondence gives the
   reverse dimension bound. Its inverse image `q` in `R` is minimal over
   `p + (x)` and satisfies `dim(R/q) = dim(R/p) - 1`.
7. By `lem-weil-pbc-associated-prime-power-quotient`, some `n ≥ 1` makes `q`
   associated to `M/x^n M`. The power remains a nonzerodivisor in the maximal
   ideal. By `lem-weil-pbc-depth-drops-by-one`, this finite quotient has depth
   one less. Apply induction at `q` and the dimension equality to conclude.
-/
theorem depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  sorry

end IsLocalRing
