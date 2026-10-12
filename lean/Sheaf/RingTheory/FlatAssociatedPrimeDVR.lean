module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Associated-prime localizations of a flat algebra with reduced quotient

Source: Stacks Project, Algebra, Tag 032Z, the algebraic argument after reducedness.
(blueprint: lem-weil-pbc-flat-associated-prime-dvr)
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- The algebraic part of Stacks Project, Algebra, Tag 032Z, after establishing
Noetherianity, flatness, and reducedness of the quotient. No completion or analytic
unramifiedness is used in this part.
(blueprint: lem-weil-pbc-flat-associated-prime-dvr)

Proof: Put B = A/pA and C = A_q. Write q = Ann(z) with z in B. Since q is proper,
z is nonzero. Lift z to a in A. If a belonged to q, z squared would be zero,
contrary to reducedness. Thus a is invertible in C. The inclusion pA <= q follows
because pA kills B. For b in q, ba belongs to pA; division by a in C gives qC = pC.
For s outside p, multiplication by s on R/p is injective. Tensoring with the flat
R-module A shows that multiplication by s on B is injective, so its image cannot
kill z. Consequently the image of every s outside p is outside q.
Choose x in p whose nonzero image generates pR_p, by writing a uniformizer of the
DVR R_p as a fraction and discarding its unit denominator. For each of the finitely
many generators of p, clear the equality expressing it as a multiple of x in R_p.
Multiply all clearing denominators to get s outside p with sp contained in xR.
Since s is invertible in C, this gives qC = pC = xC.
The finitely generated ideal K = Ann_R(x) vanishes upon localization at p, because
R_p is a domain and x/1 is nonzero. Clearing denominators on generators of K gives
t outside p with tK = 0. Flatness preserves the exact multiplication sequence,
so Ann_A(x) = KA. As t is invertible in C, x is a nonzerodivisor in C.
The ring C is Noetherian and local. Krull intersection for its maximal ideal (x)
shows that the intersection of its powers is zero. For any nonzero b, choose the
largest n for which b belongs to (x^n), and write b = x^n u. Maximality forces u
outside the maximal ideal, hence u is a unit. Products of nonzero elements are
nonzero since x is a nonzerodivisor. Thus C is a domain. In any nonzero ideal choose
an element of least such exponent n; every other element is divisible by x^n, so
the ideal is (x^n). Finally x is nonzero and generates the maximal ideal, which
therefore is nonzero. These facts give the DVR structure. -/
theorem isDiscreteValuationRing_atPrime_of_flat_reduced_quotient
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsReduced (A ⧸ p.map (algebraMap R A))]
    (q : Ideal A) [q.IsPrime]
    (hq : ∃ z : A ⧸ p.map (algebraMap R A),
      q = (⊥ : Submodule A (A ⧸ p.map (algebraMap R A))).colon {z}) :
    ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  sorry

end AdicCompletion
