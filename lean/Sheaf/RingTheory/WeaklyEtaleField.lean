/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Separable
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.RingTheory.FiniteTypeAlgebraFiniteSpectrum
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-! # Weakly étale algebras over a field

Source: Stacks Project, Tag 092Q, lemma-absolutely-flat-over-field
(blueprint: lem-weil-pbc-weak-etale-field).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace Algebra

/-- Every finitely generated subalgebra of a weakly étale field algebra is finite étale;
the algebra is ind-étale and reduced, with separable algebraic residue fields.
Source: Stacks Project, Tag 092Q (blueprint: lem-weil-pbc-weak-etale-field).

Proof:
1. Every module over `k` is free and flat, so the common bound in
   `lem-weil-pbc-weak-etale-tor` is zero and every `B`-module is flat. Localization and
   composition (`lem-weil-pbc-localization-ring-weakly-etale`,
   `lem-weil-pbc-ind-etale-stability`) give the same conclusion over each `B_p`.
2. For a nonunit `b` of `B_p`, flatness of `B_p/(b)` and
   `lem-exc-flat-quotient-element-equation` give `b = b*e` with `e ∈ (b)`.
   The element `1-e` is a unit, so `b=0`. Thus `B_p` is a field and equals `κ(p)`.
3. A nilpotent vanishes in every `B_p`. If it were nonzero its proper annihilator
   would lie in a prime (`lem-weil-pbc-minimal-prime-over-proper-ideal`), contradicting
   localization vanishing. Thus `B` is reduced. Apply
   `lem-weil-pbc-weakly-etale-field-separable` to obtain separable algebraic `κ(p)`.
4. A finitely generated subalgebra `A` is reduced. Lift a minimal prime of `A` to `B`
   by `lem-weil-pbc-injective-minimal-prime-lift`. Its quotient embeds in the corresponding
   `B_p`, since the localization map has kernel `p`. An algebraic domain over `k` is a
   field: a minimal-degree relation for a nonzero element has nonzero constant term and
   expresses its inverse. Thus every minimal prime of `A` is maximal, with separable
   algebraic quotient (minimal polynomials are unchanged by the embedding).
5. `lem-weil-pbc-finite-type-algebra-noetherian` makes `A` Noetherian, and
   `lem-weil-pbc-noetherian-finitely-many-minimal-primes` gives finitely many minimal primes.
   `lem-weil-pbc-prime-contains-minimal-prime` shows all primes are among these maximal
   ideals. Apply `pqf-lem-finite-type-algebra-finite-spectrum` to get module finiteness.
6. By `lem-weil-pbc-reduced-noetherian-total-ring-fractions`, the total fraction ring is
   the product of the localizations at these primes. Nonzerodivisors avoid every minimal
   prime (`lem-pc-minimal-prime-avoids-nonzerodivisor`), hence every prime, and are units
   by `lem-weil-pbc-minimal-prime-over-proper-ideal`. Thus `A` equals its total fraction
   ring. The factors equal the separable field quotients from step 4 and are finite
   by step 5. `lem-sc-finite-etale-algebra-criterion` makes `A` finite étale.
7. The finitely generated subalgebras form a directed system under inclusion: take
   unions of finite generating sets. Every element belongs to its singly generated
   subalgebra. Compatible maps glue uniquely on this union, respecting operations
   by passing to a common subalgebra. This filtered presentation gives `IndEtale`
   by `def-weil-pbc-ind-etale-algebra`. For `B=0`, the zero algebra is the sole
   subalgebra, prime quantification is empty, and the product decomposition is empty.
-/
theorem weaklyEtale_field
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    [Algebra.WeaklyEtale k B] :
    (∀ A : Subalgebra k B, A.FG → Module.Finite k A ∧ Algebra.Etale k A) ∧
      Algebra.IndEtale k B ∧
      IsReduced B ∧
      (∀ p : PrimeSpectrum B,
        Algebra.IsSeparable k p.asIdeal.ResidueField ∧
          Algebra.IsAlgebraic k p.asIdeal.ResidueField) := by
  sorry

end Algebra
