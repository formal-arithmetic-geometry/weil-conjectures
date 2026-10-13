/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.DirectedUnionSubringsFlatModule

/-! # Flatness of polynomial local quotients over finite coefficient subrings

Source: Stacks Project, Algebra, Tag 00SV, second paragraph of the proof, and Tag 05UU (2).
(blueprint: lem-weil-pbc-polynomial-local-flat-quotient-descent).
-/

@[expose] public section

universe u

namespace RingTheory

/-- Flatness of a fixed prefix quotient passes from finite type coefficient subrings to
an arbitrary coefficient ring. No complete-intersection or regularity assumption is used.
Source: Stacks Project, Algebra, Tag 00SV, second paragraph of the proof; Tag 05UU (2).
(blueprint: lem-weil-pbc-polynomial-local-flat-quotient-descent).

Proof: Index by finite type integer subrings `B` containing `R₀`, ordered by inclusion.
The index is nonempty (`R₀` is a stage) and directed (adjoin the finite generating sets
of two stages). Its union is `R`: adjoin any requested element to generators of `R₀`.
Contract `Q` to each polynomial ring over `B`. Subring inclusions preserve the complements
of the contracted primes, so they induce compatible localization maps. These maps carry
each displayed equation to the next stage equation, hence induce semilinear maps on the
prefix quotients and compatible maps to the full quotient. Every class of a fraction
comes from a stage containing its finitely many numerator and denominator coefficients.
If a stage class `h/s` vanishes in the full quotient, clear denominators in its expression
as a linear combination of the finitely many prefix equations: there are polynomials
`aⱼ`, and `t,u` outside `Q`, with `u * (t*h - s*∑ aⱼ*fⱼ) = 0`. Enlarge the stage by
all their coefficients. The identity holds already in this polynomial subring, whose
inclusion is injective; it makes the class vanish at the enlarged stage. The modules
therefore satisfy representation and eventual vanishing of Tag 05UU (2), along with the
transition identities, and stage flatness is exactly `hstage`. Apply that lemma.
For `i=0` the ideal is zero; for `i≥c` the prefix is the full finite list. Zero quotient
modules cause no problem. No flatness of the coefficient-subring inclusions is assumed.
-/
theorem flat_polynomial_local_quotient_of_finiteType_subrings
    {R : Type u} [CommRing R] (R₀ : Subring R)
    (hR₀ : Algebra.FiniteType ℤ R₀) {n c : ℕ}
    (f₀ : Fin c → MvPolynomial (Fin n) R₀)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime] (i : ℕ)
    (hstage : ∀ (B : Subring R) (hB : R₀ ≤ B), Algebra.FiniteType ℤ B →
      Module.Flat B
        (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)) ⧸
          Ideal.ofList (((List.ofFn
            (fun j ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ j))).map
              (algebraMap (MvPolynomial (Fin n) B)
                (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype))))).take i))) :
    Module.Flat R (Localization.AtPrime Q ⧸
      Ideal.ofList (((List.ofFn (fun j ↦ MvPolynomial.map R₀.subtype (f₀ j))).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))).take i)) := by sorry

end RingTheory
