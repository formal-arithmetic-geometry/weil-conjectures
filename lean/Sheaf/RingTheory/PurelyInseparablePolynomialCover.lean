/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# A coefficient-root cover for a purely inseparable polynomial field extension

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), second assertion.
-/

@[expose] public section

universe u
set_option autoImplicit false

/-- A finite purely inseparable extension of `Frac(R[X])` embeds in the fraction
field of a polynomial ring over the integral closure of R in a finite coefficient
extension. The map sends X to a positive power of the new variable. No Japanese,
Noetherian, or normality hypothesis on R is required.

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), coefficient-root cover
in the proof of the second assertion.
(blueprint: lem-weil-pbc-purely-inseparable-polynomial-cover).

Proof: Put K = Frac(R), F = Frac(R[X]), and identify F with K(x) by clearing
coefficient denominators. Take a finite F-basis of L and choose a common q = p^e
such that its q-th powers lie in F. Express these powers as quotients of polynomials
over K. Inside an algebraic closure of L, adjoin to K the q-th roots of their finitely
many coefficients. Their generated algebra is spanned by monomials with each exponent
less than q, hence is finite dimensional; being a domain over a field, it is a field E.
Choose t with t^q = x. Taking coefficient roots in each numerator and denominator
produces polynomials in t whose q-th powers are the original numerator and denominator.
The denominator is nonzero, since its q-th power is nonzero. Injectivity of iterated
Frobenius identifies each original basis element with the quotient of these rooted
polynomials. Hence all of L lies in E(t). The element t is transcendental over E:
otherwise E/K finite would make x = t^q algebraic over K, contradicting the
transcendence of x. Let A be the integral closure of R in E. Because E/K is finite,
E is the fraction field of A. Clearing coefficient denominators then identifies
Frac(A[T]) with E(T); evaluation at t gives an isomorphism E(T) with E(t). Composing
the embedding L into E(t) with its inverse yields the ring map f. On R[X] it is
evaluation with r mapped to its constant image in A[T] and X mapped to T^q, exactly
the displayed equation. The algebraic closure, its finite subfields and Frac(A[T])
all lie in Type u; no universe enlargement is needed. For the trivial extension,
take q = 1, E = K and the ordinary fraction-field identification. -/
theorem exists_purelyInseparable_polynomial_cover
    (R : Type u) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing (Polynomial R)) p]
    (L : Type u) [Field L] [Algebra (FractionRing (Polynomial R)) L]
    [Algebra (Polynomial R) L] [IsScalarTower (Polynomial R) (FractionRing (Polynomial R)) L]
    [FiniteDimensional (FractionRing (Polynomial R)) L]
    [IsPurelyInseparable (FractionRing (Polynomial R)) L] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra (FractionRing R) E) (_ : Algebra R E)
      (_ : IsScalarTower R (FractionRing R) E) (_ : FiniteDimensional (FractionRing R) E),
    ∃ q : ℕ, 0 < q ∧
      ∃ f : L →+* FractionRing (Polynomial (integralClosure R E)),
        ∀ a : Polynomial R,
          f (algebraMap (Polynomial R) L a) =
            algebraMap (Polynomial (integralClosure R E))
              (FractionRing (Polynomial (integralClosure R E)))
              (Polynomial.eval₂RingHom
                (Polynomial.C.comp (algebraMap R (integralClosure R E)))
                (Polynomial.X ^ q) a) := by
  sorry
