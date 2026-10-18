/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Norm.Defs

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Valuation of a field norm over a finite semilocal DVR algebra

Source: Stacks Project, Algebra, Tag 02MJ (`lemma-finite-extension-dim-1`), specialized
to discrete valuation rings (blueprint: lem-exc-dvr-norm-valuation-sum).

The normalized integer valuation is `WithZero.log (Ring.ordFrac R x)`: the order of a
uniformizer is `WithZero.exp 1` by `Ring.ordFrac_irreducible`, so its integer value is `1`.
The field norm is `Algebra.norm`, the determinant of multiplication by the element.
-/

@[expose] public section

universe u v w z

namespace IsDiscreteValuationRing

/-- The valuation of the norm is the sum of the local valuations weighted by residue degrees.
Source: Stacks Project, Algebra, Tag 02MJ (blueprint: lem-exc-dvr-norm-valuation-sum).

Here `A / q.under A` is the residue field of `A` by `hcontract`; its canonical algebra
structure on `B / q` is induced by the given inclusion. The fraction field of each localization
is canonically `FractionRing B`; `IsLocalization.algEquiv` transports `y` from the given `L`.

Proof, following the six steps of the node:

1. The `K`-span of the image of `B` in `L` is finite-dimensional, since finite
   `A`-generators span it (`def-weil-finitely-generated-module`,
   `def-weil-finite-dimensional-subspace`). It is closed under multiplication and contains
   `1`. Multiplication by a nonzero element is injective, hence surjective on this
   finite-dimensional space. Thus the span is a field containing `B`, so it is all of `L`.
   Consequently `B` is a finite `A`-lattice in `L`.
2. Put `H = B ∩ yB` inside `L`. Multiplication by `y` is a `K`-linear isomorphism.
   Apply `lem-exc-dvr-lattice-distance-determinant` to the lattice `B`: the modules
   `M₊ = B / H` and `M₋ = yB / H` have finite `A`-length, and their length difference is
   the normalized order of the determinant, namely `Algebra.norm K y`
   (`def-weil-endomorphism-determinant`; Stacks Tags 02MI and 02MG).
3. A strict chain of `B`-submodules is also a strict chain of `A`-submodules, so both
   quotients have finite `B`-length (`def-weil-pbc-module-length`). Apply
   `lem-exc-semilocal-restriction-length` to each and subtract the finite sums in `ℤ`.
   This expresses the norm order as the residue-degree-weighted sum of local length
   differences (Stacks Tag 02M0).
4. For each maximal ideal `q`, put `R = B_q`. The inclusions `B ⊆ R ⊆ L` identify
   `Frac(R)` with `L`. Clearing denominators gives `H_q = R ∩ yR`: if
   `x = b/s = yc/t`, then `stx = tb = ysc` belongs to `H`. By
   `lem-weil-pbc-localization-module-exact` and `def-weil-pbc-module-localization`,
   localization of the quotient sequences identifies `(M₊)_q` with `R / (R ∩ yR)` and
   `(M₋)_q` with `yR / (R ∩ yR)`, preserving their lengths.
5. A DVR is a Noetherian PID (`def-sc-discrete-valuation-ring`,
   `lem-weil-pbc-pid-noetherian-normal`). By
   `lem-weil-pbc-dvr-unit-times-uniformizer-power`, its nonzero ideals are powers of a
   uniformizer `t`. The ideals above `(t^n)` are exactly `(t^j)` for `0 ≤ j ≤ n`, so
   `length_R(R / t^n R) = n`, including `n = 0`. Write `y = u t^r`, with `r : ℤ`,
   by applying unit-times-power factorization to a numerator and denominator; the
   exponent is unique since `t` is a nonunit. If `r ≥ 0`, the two local lengths are
   `r` and `0`. If `r = -n < 0`, they are `0` and `n`, using multiplication by `t^n`
   to identify `yR / R` with `R / t^n R`. Their difference is therefore the normalized
   valuation `WithZero.log (Ring.ordFrac R y)` (Stacks Tags 02MD and 00PD).
6. Substitute these local differences into the weighted sum from step 3. This proves
   the asserted equality for every nonzero `y`, including units and negative valuations.
-/
theorem norm_valuation_sum
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type w) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (L : Type z) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [Fintype (MaximalSpectrum B)]
    (hcontract : ∀ q : MaximalSpectrum B,
      q.asIdeal.under A = IsLocalRing.maximalIdeal A)
    [∀ q : MaximalSpectrum B, IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Module.Finite (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)]
    (y : Lˣ) :
    WithZero.log (Ring.ordFrac A (Algebra.norm K (y : L))) =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) : ℤ) *
          WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
            (IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B) (y : L))) := by
  sorry

end IsDiscreteValuationRing
