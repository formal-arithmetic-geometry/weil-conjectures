/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# A regular sequence at a prime spreads to a principal neighbourhood

Source: literature/stacks-project/algebra.tex, Tag 061L, lemma-regular-sequence-in-neighbourhood
(specializing the finite module to the ring; blueprint:
lem-exc-regular-sequence-principal-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/--
Source: Stacks Project, algebra.tex, Tag 061L, lemma-regular-sequence-in-neighbourhood,
specializing the finite module to the ring.
(blueprint: lem-exc-regular-sequence-principal-neighbourhood)

Proof, following the six steps of the node:

1. Put `I_i = (x_1, ..., x_i)` and `Q_i = R/I_i`, including `I_0 = 0`.
   Let `K_i` be the kernel of multiplication by `x_i` on `Q_{i-1}`. Each quotient
   is cyclic, hence finite. By `lem-weil-pbc-noetherian-submodule-finite`, each
   kernel has finitely many generators; this is where Noetherianity is used.
2. By `lem-weil-pbc-localization-module-exact`, localizing the quotient sequence
   identifies `T⁻¹Q_i` with `T⁻¹R/(x_1/1, ..., x_i/1)`. The map sends
   `(a + I_i)/t` to the class of `a/t`. The localized quotient map is surjective
   by lifting numerators, and its kernel is the localized ideal: a numerator in
   `I_i` is a sum of multiples of the `x_j`, and conversely such a sum has a common
   denominator and numerator in `I_i`. The fraction formulas of
   `def-weil-pbc-module-localization` show these identifications commute with
   multiplication. Use both the prime complement and the powers of `g`, as in
   `def-weil-pbc-localization-at-prime` and `def-weil-ring-localization-away`.
3. Localize the kernel sequence at the prime. Exactness and the assumed
   regularity (`def-weil-pbc-regular-sequence`) make multiplication on the
   localized quotients injective, so every localized `K_i` is zero.
4. The module-localization zero criterion supplies, for each kernel generator,
   an annihilator outside `p`. Take their finite product `g`, or `1` for the
   empty indexing set. Primality gives `g ∉ p`. Every chosen annihilator divides
   `g`, so `g` kills all generators and hence each `K_i`. Localizing at powers
   of `g` therefore kills every `K_i`, simultaneously.
5. Apply localization exactness again at powers of `g`. The vanished kernels
   and the quotient identifications of step 2 show that every successive
   multiplication by `x_i/1` is injective in the principal localization.
6. For the final nonzero quotient, each `x_i` belongs to `p`: otherwise it is a
   unit at `p`, contradicting the assumed nonzero final quotient. If `1` were
   in the ideal of their images after inverting `g`, a common denominator
   would give `1 = (∑ a_i*x_i)/g^N`. The equality criterion of
   `def-weil-ring-localization-away` gives `g^k*(g^N - ∑ a_i*x_i) = 0`, so
   `g^(N+k)` belongs to `p`, contradicting `g ∉ p`. For the empty sequence use
   the empty sum, `N = 0`, and `g = 1`. Together with step 5 this is exactly
   regularity, including the nonzero-quotient clause.
-/
theorem exists_isRegular_localizationAway_of_isRegular_localizationAtPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime]
    (r : ℕ) (x : Fin r → R)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (List.ofFn (fun i ↦ algebraMap R (Localization.AtPrime p) (x i)))) :
    ∃ g : R, g ∉ p ∧
      RingTheory.Sequence.IsRegular (Localization.Away g)
        (List.ofFn (fun i ↦ algebraMap R (Localization.Away g) (x i))) := by
  sorry

end RingTheory
