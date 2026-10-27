module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Sheaf.Order.ControlledExponentSequenceLength

/-! # Uniform degree bounds for homogeneous initial ideals

Source: Dube, The Structure of Polynomial Ideals and Groebner Bases,
SIAM J. Comput. 19 (1990), Theorem 8.2 and Corollary 8.3, printed p.773.
(blueprint: lem-sfb-bounded-homogeneous-groebner-degree)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace MonomialOrder

/-- For fixed positive numbers of variables and generator degree bound, a single positive
bound works over every field and every monomial order. The resulting finite family consists
of nonzero homogeneous ideal elements, and their leading monomials generate the initial
ideal. The zero ideal admits the empty family and the unit ideal admits the family `1`.

Source: Dube, The Structure of Polynomial Ideals and Groebner Bases,
Theorem 8.2 and Corollary 8.3, printed p.773; only existence of a bound is asserted here.
(blueprint: lem-sfb-bounded-homogeneous-groebner-degree)

Proof (the six DAG steps, an agent existence-only argument rather than Dube's numerical
cone-decomposition bound):
1. Treat the zero and unit ideals using the empty family and `1`. Otherwise discard zero
   generators and divide the remaining homogeneous generators by their leading coefficients.
   This gives a possibly infinite monic generating set B0, without changing degrees or
   leading exponents. Apply lem-sfb-controlled-exponent-sequence-length with
   h(i) = 2^(i+1) D to obtain L, and put G = 2^L D. These choices depend only on r and D.
2. For a homogeneous polynomial p of degree e, apply MonomialOrder.div
   (lem-sfb-monomial-order-polynomial-division). In its division identity retain degree e:
   replace each coefficient q_b by its component of degree e - deg(b), using zero for
   negative degrees, and retain the degree-e component of the remainder. Every retained
   product has support contained in that of q_b b, so its leading exponent is at most
   LM(p). The projected remainder is homogeneous or zero and has support avoiding every
   LM(b) coordinatewise. It lies in (B) whenever p does, by the division identity.
3. Maintain a monic homogeneous set Bt generating J, with degrees at most 2^t D. If every
   pair has the strict standard representation in
   lem-sfb-buchberger-standard-representation-criterion, stop. Otherwise choose a failing
   pair b,c. For lambda = LM(b) sup LM(c), its S-polynomial is homogeneous of degree
   |lambda| <= deg(b) + deg(c) <= 2^(t+1) D, and its top terms cancel. Divide as in step 2.
   Its remainder v cannot vanish, since a zero remainder supplies the missing strict
   representation. Adjoin v/LC(v); it belongs to J, has the required degree bound, and
   its leading exponent dominates no leading exponent of Bt. The invariants persist.
4. The leading exponent alpha_i adjoined at step i has coordinate sum at most h(i).
   For i < j, alpha_i is already present when alpha_j is adjoined, so reduction implies
   alpha_i is not coordinatewise at most alpha_j. The controlled-sequence bound gives
   at most L additions. Failure to stop through step L would give L+1 such exponents,
   so finite recursion stops at some t <= L, without enumerating the pairs.
5. Apply lem-sfb-buchberger-standard-representation-criterion at the stopping stage:
   every nonzero element of J has leading monomial divisible by one from Bt. These
   monomials therefore generate the initial ideal; the reverse inclusion uses Bt in J.
6. All degrees in Bt are at most 2^t D <= G. Each leading exponent has every coordinate
   at most G, so only finitely many leading exponents occur. Choose one member of Bt
   for each occurring exponent and enumerate the resulting finite set by Fin s. Its
   leading monomials generate the same initial ideal and its elements retain homogeneity,
   nonvanishing, membership and degree bounds. No characteristic or degree-compatibility
   assumption on the order has been used. -/
theorem exists_uniform_homogeneous_groebner_degree_bound
    (r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    ∃ G : ℕ, 1 ≤ G ∧
      ∀ (k : Type u) [Field k] (J : Ideal (MvPolynomial (Fin r) k))
        (m : MonomialOrder.{0, v} (Fin r)),
        (∃ B : Set (MvPolynomial (Fin r) k),
          Ideal.span B = J ∧
          ∀ f ∈ B, f.IsHomogeneous f.totalDegree ∧ f.totalDegree ≤ D) →
        ∃ (s : ℕ) (g : Fin s → MvPolynomial (Fin r) k),
          (∀ i, g i ∈ J ∧ g i ≠ 0 ∧
            (g i).IsHomogeneous (g i).totalDegree ∧ (g i).totalDegree ≤ G) ∧
          Ideal.span ((fun f : MvPolynomial (Fin r) k ↦
            MvPolynomial.monomial (m.degree f) (1 : k)) ''
              {f : MvPolynomial (Fin r) k | f ∈ J ∧ f ≠ 0}) =
            Ideal.span (Set.range (fun i : Fin s ↦
              MvPolynomial.monomial (m.degree (g i)) (1 : k))) ∧
          (J = ⊥ → s = 0) ∧
          (J = ⊤ → s = 1 ∧ ∀ i : Fin s, g i = 1) := by
  sorry

end MonomialOrder
