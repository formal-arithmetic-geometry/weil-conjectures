/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.RingTheory.NormalizationIntegralClosureKrull
import Sheaf.TraceFormula.AlmostFiniteResidueFieldDegree

/-!
# Noetherian normalizations from Japanese nonzero prime quotients

Source: Marot, *Sur les anneaux universellement japonais* (1975), Lemma 1.2,
printed pp. 104–105, and its application in Proposition 2.3, printed p. 107
(blueprint: lem-per-japanese-quotients-noetherian-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace RingTheory

/-- If every nonzero prime quotient of a Noetherian domain is Japanese, its integral
closure in every finite extension of its fraction field is Noetherian. Neither
separability of the extension nor normality of the base is assumed.

Source: Marot, *Sur les anneaux universellement japonais* (1975), Lemma 1.2,
printed pp. 104–105; Proposition 2.3, printed p. 107
(blueprint: lem-per-japanese-quotients-noetherian-normalization).

Proof:
1. Fix a finite `K`-basis of `L`. Clear the denominators in monic equations over `K`
   to scale its basis vectors to elements integral over `R`. Their generated algebra
   `B` is finite over `R` by `lem-sc-finite-generated-integral-subring`, hence
   Noetherian by `lem-weil-pbc-finite-algebra-noetherian`. It is a domain with
   fraction field `L`, since the original basis vectors are fractions of its elements.
2. Write `T = integralClosure R L`. The algebra `B` is integral over `R`, and
   integrality transitivity (`lem-weil-pbc-integral-transitive`) identifies `T` with
   the integral closure of `B` in `L`. The birational Mori–Nagata theorem
   `lem-trf-normalization-integral-closure-krull` therefore makes `T` a Krull domain.
3. For a height-one prime `P` of `T`, choose nonzero `z ∈ P`. A monic equation of
   least positive degree for `z` over `R` has nonzero constant term: otherwise
   cancel `z` to obtain an equation of smaller degree. That constant term belongs
   to `P ∩ R`, so `q = P ∩ R` is nonzero and the hypothesis makes `R/q` Japanese.
4. By `lem-trf-almost-finite-residue-field-degree`, `Frac(T/P)` is finite over
   `Frac(R/q)`. The Japanese condition (`def-weil-pbc-japanese-domain`) makes the
   integral closure `U` of `R/q` in `Frac(T/P)` finite over `R/q`. Reduction of
   monic equations embeds `T/P` into `U`. The quotient `R/q` is Noetherian by
   `lem-weil-pbc-surjective-image-noetherian`, so
   `lem-weil-pbc-noetherian-submodule-finite` makes `T/P` finite over `R/q`, and
   `lem-weil-pbc-finite-algebra-noetherian` makes `T/P` Noetherian.
5. Every height-one prime quotient of the Krull domain `T` is thus Noetherian.
   Apply `lem-per-krull-height-one-quotients-noetherian` to conclude. -/
theorem isNoetherianRing_integralClosure_of_isN2_nonzero_prime_quotients
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    (hR : ∀ (q : Ideal R) [q.IsPrime], q ≠ ⊥ →
      IsN2 (R ⧸ q) (FractionRing (R ⧸ q))) :
    IsNoetherianRing (integralClosure R L) := by
  sorry

end RingTheory
