/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.RingTheory.FiniteType
public import Sheaf.RingTheory.JapaneseDomain
public import Sheaf.RingTheory.NagataRing

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.PolynomialResidueFiniteCoefficientModel

/-!
# A normalization criterion for universally Japanese rings

Source: Stacks Project, Algebra, Lemma 10.162.3 (Tag 0351),
`lemma-check-universally-japanese`
(blueprint: lem-exc-universally-japanese-n1-criterion).
-/

@[expose] public section

universe u

/-- A commutative ring is universally Japanese if every finite type domain algebra over
it has finite normalization in its fraction field.
Source: Stacks Project, Algebra, Lemma 10.162.3 (Tag 0351),
`lemma-check-universally-japanese`
(blueprint: lem-exc-universally-japanese-n1-criterion).

Proof:
1. Fix a finite type domain algebra `S` over `R`, put `K = FractionRing S`, and take a
   finite extension `L/K`. In `S[X]`, the ideal `r = (X)` is nonzero and prime and
   contracts to zero in `S`. Evaluation at zero identifies its residue field with `K`:
   the residue of `f/g` maps to `f(0)/g(0)`, and the inverse sends `a/b` to the residue
   of the quotient of constant polynomials. The identity `f = f(0) + X h` verifies that
   these maps are inverse. Transport the finite extension `L/K` along this identification.
2. Apply `lem-weil-pbc-polynomial-residue-finite-coefficient-model` at `r`. It produces
   a finite `S`-subalgebra `S'` of `L` and a residue field isomorphic to `L`, which is a
   fraction field of `S'`. Transporting the fraction presentations makes `L` itself a
   fraction field of `S'`. Finite algebra generators of `S/R` together with finite module
   generators of `S'/S` generate `S'` as an `R`-algebra. Since `S'` is a subring of `L`,
   it is a domain. The hypothesis therefore makes `S'` N-1.
3. The integral closure `S''` of `S'` in `L` is finite over `S'` by N-1
   (`def-weil-pbc-japanese-domain`). Since `S'` is finite over `S`, finite-module
   transitivity (`lem-weil-pbc-finite-module-over-finite-algebra`) makes `S''` finite over `S`.
4. The integral closures of `S` and `S'` in `L` coincide. A monic equation over `S` is
   also one over `S'`. Conversely, `S'` is integral over `S` by
   `lem-weil-pbc-finite-algebra-is-integral`, and integrality of `S''` over `S'` follows
   from `def-weil-pbc-integral-closure`. Apply `lem-weil-pbc-integral-transitive` to
   `S → S' → S''`. Thus the integral closure of `S` in every finite `L/K` is finite
   over `S`, so `S` is N-2. Varying `S` proves that `R` is universally Japanese. -/
theorem isUniversallyJapanese_of_forall_isN1 (R : Type u) [CommRing R]
    (h : ∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
      [Algebra.FiniteType R S], IsN1 S (FractionRing S)) :
    IsUniversallyJapanese R := by
  sorry
