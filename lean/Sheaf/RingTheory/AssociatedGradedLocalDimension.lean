module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Regular
import Sheaf.RingTheory.ReesAssociatedGradedChart

/-! # Associated graded rings determine local dimension

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose III,
Corollary 5.4(i) and proof, pp. 42--43 (Matsumura, Theorem 15.9).
(blueprint: lem-per-associated-graded-local-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- A graded isomorphism of the associated graded rings of ideals contained in the
maximal ideals of Noetherian local rings implies equality of their Krull dimensions.
The ideals may be zero and need not be primary for the maximal ideals.
Source: ILO, Expose III, Corollary 5.4(i), pp. 42--43, local-ring formulation.
(blueprint: lem-per-associated-graded-local-dimension).

Proof: For (R, n), I, put G = gr_I(R) and m = (n/I) plus all positive degrees.
1. In E = R[t,I/t], constant coefficient modulo n is a surjective ring map to R/n.
Its kernel M is maximal and contains t. Finite generation of I makes E finite type,
hence Noetherian by lem-weil-pbc-finite-type-algebra-noetherian. Localize at M using
def-weil-pbc-localization-at-prime to obtain A. Laurent coefficient shifts show t
is a nonzerodivisor in A, and t belongs to its maximal ideal.
2. By lem-weil-pbc-noetherian-local-finite-krull-dimension, dim R = d is finite.
A longest prime chain of R ends at n. Intersect its Laurent extensions with E;
constant coefficients detect strictness. All these primes lie in M, and the last
is strictly smaller than M since it omits t. Localization preserves the chain,
so d + 1 is at most dim A.
3. Apply lem-per-laurent-subalgebra-dimension-bound to E inside R[t,t^-1].
Then dim A is at most dim E, which is at most d + 1. Thus dim A = d + 1.
4. By lem-pur-rees-associated-graded-chart, G is E/(t), sending [a]_q to [a/t^q].
This identifies m with M/(t). By lem-weil-pbc-localization-at-prime-of-quotient,
G localized at m is A/(t). Apply lem-weil-pbc-dimension-quotient-nonzerodivisor
in A to conclude that dim G_m = d.
5. Repeat for (T, p), J. The given isomorphism maps each homogeneous summand onto
the summand of the same degree (the image equality below). Its degree-zero
restriction identifies the local rings R/I and T/J and hence their maximal ideals.
It therefore identifies m and the corresponding homogeneous maximal ideal of gr_J(T).
The localized rings are isomorphic, so their prime chains have the same lengths.
Their dimensions, already identified with dim R and dim T, are equal. -/
theorem ringKrullDim_eq_of_associatedGraded_iso
    {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T] [IsLocalRing R] [IsLocalRing T]
    (I : Ideal R) (J : Ideal T)
    (hI : I ≤ IsLocalRing.maximalIdeal R) (hJ : J ≤ IsLocalRing.maximalIdeal T)
    (e : associatedGraded I ≃+* associatedGraded J)
    (hgraded : ∀ n : ℕ,
      Set.image e (Set.range (DirectSum.of (associatedGradedPiece I) n)) =
        Set.range (DirectSum.of (associatedGradedPiece J) n)) :
    ringKrullDim R = ringKrullDim T := by
  sorry

end Ideal
