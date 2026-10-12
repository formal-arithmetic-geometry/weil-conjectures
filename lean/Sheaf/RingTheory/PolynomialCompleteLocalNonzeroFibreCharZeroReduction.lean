/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.RingTheory.GRing
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Sheaf.RingTheory.FiniteRingMapQuasiFinite
import Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FibreRingNoetherian

/-! Reduction to a regular complete local coefficient subring.
Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraphs 3--4.
(blueprint: lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero-reduction)
-/

@[expose] public section

universe u

namespace Polynomial

/-- The Cohen-subring and finite-map part of the characteristic-zero formal-fibre argument.
Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraphs 3--4.
(blueprint: lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero-reduction)

Proof:
1. By 032D take an actual subring A₀ of A that is regular local, complete at its
   maximal ideal, and finite in A. It is Noetherian and a domain. The injections
   A₀ → A → Frac(A) imply CharZero A₀. Its maximal ideal is the contraction of
   that of A. Use the inherited ring structure and the subring inclusion.
2. The polynomial extension A₀[X] → A[X] is finite: constant polynomials of a
   finite A₀-module generating set of A generate A[X] over A₀[X]. It is thus
   integral and finite type, and quasi-finite at q. Contract q and r to q₀ and r₀.
   Integral contraction makes q₀ maximal, and contraction preserves primality and
   containment. Composing coefficient inclusions proves the stated contractions.
   Moreover r₀ is nonzero: after inverting A₀ minus zero, the extension becomes
   K₀[X] → K[X] for a finite field extension K/K₀. A nonzero polynomial in r has
   a nonzero norm in K₀[X] belonging to the contracted ideal; clear denominators.
3. Suppose the contracted formal fibre is regular. It is Noetherian by
   Noetherianity of completions and fibre rings. Its residue field has characteristic
   zero: A₀ embeds into A₀[X]/r₀, hence into its fraction field κ(r₀).
   Every purely inseparable extension of this field is trivial; the algebra map
   is bijective, so tensoring with it is an isomorphic ring. Regularity transports
   through that isomorphism. The contracted fibre is therefore geometrically regular.
4. Apply 07PP(1) to the finite polynomial map and r ≤ q. It transfers this geometric
   regularity to the original fibre and supplies exactly the displayed implication.
   The conclusion here constructs no definition from an arbitrary existence witness;
   the main theorem eliminates this existence statement only to prove a proposition.
-/
theorem completeLocalNonzeroFibreCharZero_reduction
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    [CharZero (Localization.AtPrime (⊥ : Ideal A))]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsNoetherianRing A₀)
      (_ : IsRegularLocalRing A₀) (_ : CharZero A₀)
      (_ : IsLocalRing A₀) (_ : IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀)
      (q₀ r₀ : Ideal (Polynomial A₀)) (_ : q₀.IsMaximal) (_ : r₀.IsPrime),
      q₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) = IsLocalRing.maximalIdeal A₀ ∧
      r₀ ≤ q₀ ∧ r₀ ≠ ⊥ ∧
      r₀.comap (Polynomial.C : A₀ →+* Polynomial A₀) = ⊥ ∧
      (IsRegularRing (r₀.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q₀))
          (Localization.AtPrime q₀))) →
       Algebra.IsGeometricallyRegular r.ResidueField
        (r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)))) := by sorry

end Polynomial
