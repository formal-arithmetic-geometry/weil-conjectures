/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.KrullDimension.PID
import WeilConjectures.RingTheory.FlatFiberPrimeHeight
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg

/-!
# Height and residue transcendence degree in a polynomial algebra

Source: Stacks Project, Algebra, Tag 02IJ (`algebra-lemma-dimension-formula`),
proof, Case I (blueprint: lem-trf-polynomial-prime-height-residue-degree).

Mathlib's `Ideal.ResidueField` is a fraction field of the prime quotient.
The coefficient algebra below is induced by the constant-polynomial inclusion,
using `Ideal.ResidueField.map`. Heights take values in `ℕ∞`; `Cardinal.toENat`
preserves the finite residue transcendence degrees in this statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Polynomial

/-- The polynomial algebra has relative transcendence degree one, and the height
of any prime plus its residue transcendence degree is the base prime height plus one.
Source: Stacks Project, Algebra, Tag 02IJ (`algebra-lemma-dimension-formula`),
proof, Case I (blueprint: lem-trf-polynomial-prime-height-residue-degree).

Proof (the five steps of the DAG):
1. Apply `lem-trf-mvpolynomial-transcendence-degree` with one variable to get
   `trdeg_R R[T] = 1`. The monomials form a free R-basis, so
   `lem-weil-pbc-projective-module-flat` gives flatness. The generator T gives
   finite type, and `lem-weil-pbc-finite-type-algebra-noetherian` gives Noetherianity.
   Nonzero leading coefficients multiply to a nonzero leading coefficient, so R[T]
   is a domain.
2. Put k = kappa(p). The maps f tensor a ↦ a times the image of f and
   sum a_i T^i ↦ sum T^i tensor a_i identify R[T] tensor_R k with k[T].
   `lem-weil-pbc-fibre-ring-primes-bijection` identifies Q with a fibre prime q;
   `lem-weil-pbc-fibre-ring-residue-field-iso` identifies their residue fields over k.
   For every prime a, the fraction field of A/a identifies with the residue field
   of A_a by sending the residue fraction of b/s to the class of b/s. This is
   injective since b/s lies in a A_a exactly when b lies in a, and surjective since
   every class has such a representative; the identification respects ring maps.
3. Switch tensor factors to k tensor_R R[T] and apply
   `lem-weil-pbc-flat-fiber-prime-height`: ht(Q) = ht(p) + ht(q).
   The localization dimensions used there equal prime-chain heights by
   `lem-weil-pbc-localization-dimension-chains-below-prime`.
4. `lem-sc-p1-polynomial-dimension-one` gives dim k[T] = 1. If q = 0, its height
   is zero and `lem-weil-pbc-finite-type-domain-dimension-trdeg` applied to k[T]
   gives residue transcendence degree one. If q is nonzero, the chain 0 < q
   and the dimension bound give height one and show q is maximal. Prime
   correspondence for k[T]/q then gives dimension zero. Applying the same
   dimension/transcendence-degree lemma to this finite type domain gives residue
   transcendence degree zero.
5. In both cases ht(q) + trdeg_k kappa(q) = 1. Substitute the residue-field
   identification of step 2 into the height decomposition of step 3 and add the
   residue degree. Together with step 1 this proves the two assertions.
-/
theorem height_add_trdeg_residueField_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (Q : Ideal (Polynomial R)) (p : Ideal R) [Q.IsPrime] [p.IsPrime]
    (hpQ : p = Q.comap (algebraMap R (Polynomial R))) :
    Algebra.trdeg R (Polynomial R) = 1 ∧
      Q.height + Cardinal.toENat
          (@Algebra.trdeg p.ResidueField Q.ResidueField _ _
            (Ideal.ResidueField.map p Q (algebraMap R (Polynomial R)) hpQ).toAlgebra) =
        p.height + 1 := by
  sorry

end Polynomial
