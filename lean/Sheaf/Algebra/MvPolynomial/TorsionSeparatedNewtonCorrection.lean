module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations

/-! # A Newton correction with separated parameter torsion

Source: Elkik, Solutions d'équations à coefficients dans un anneau hensélien,
I, Lemma 1, pp.555–558, especially pp.556–557; the agent-written scalar-identity
adaptation uses Gabber–Ramero, Almost Ring Theory, (5.4.4), pp.148–149.
(blueprint: lem-per-torsion-separated-newton-correction)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

/-- Scalar conormal identities give one finite Newton correction when parameter-power
 torsion vanishes sufficiently deeply. Divisibility by `t ^ n` expresses membership
 in the principal ideal `t ^ n R`; no regularity or completeness is assumed.

Source: Elkik, I, Lemma 1, pp.555–558, especially the Taylor expansion on p.556
and the torsion-intersection argument on p.557. This is the node's agent-written
adaptation using the scalar conormal identities of Gabber–Ramero (5.4.4), pp.148–149.
(blueprint: lem-per-torsion-separated-newton-correction)

Proof:
1. Put s = q - h. The inequalities give q = h + s, s > h and c ≤ s. Since
   g i belongs to J, choose u i with g i evaluated at a equal to t^q * u i.
   Set v i = t^s * u i and a' i = a i - v i. Then t^h * v i = g i evaluated
   at a, and each coordinate difference belongs to t^s R.
2. For f in J put D i = (pderiv i f)(a) and L = f(a) - sum_i D i * v i.
   Evaluation is the ring homomorphism from def-weil-pbc-mv-polynomial-ring.
   Every element of J^2 is a finite sum of products of elements of J, so its
   evaluation belongs to t^(2*q) R. Evaluating the scalar identity therefore
   gives t^h * L = t^(2*q) * w for some w.
3. The element z = L - t^(2*q-h) * w is killed by t^h and belongs to t^s R,
   hence to t^c R. The torsion hypothesis gives z = 0, without cancelling t^h.
   Thus L belongs to t^(2*q-h) R, which is contained in t^(2*s) R.
4. Expand each monomial of f at a-v. Its constant and linear terms are L:
   the linear term uses def-weil-pbc-polynomial-partial-derivative. All other
   terms contain at least two coordinates of v, hence belong to t^(2*s) R.
   The finite sum of monomials gives f(a') in t^(2*s) R. This finite Taylor
   calculation is the polynomial case of Stacks Tag 0AK3. If d = 0 the sums
   are empty and the remainder is zero, so the same argument applies.
-/
theorem exists_newton_correction_of_torsion_separated
    {R : Type u} [CommRing R] (t : R) (c : ℕ)
    (htorsion : ∀ z : R, t ^ c ∣ z → (∃ m : ℕ, t ^ m * z = 0) → z = 0)
    (d : ℕ) (J : Ideal (MvPolynomial (Fin d) R))
    (G : MvPolynomial (Fin d) R) (g : Fin d → MvPolynomial (Fin d) R)
    (hg : ∀ i : Fin d, g i ∈ J)
    (hidentity : ∀ f : MvPolynomial (Fin d) R, f ∈ J →
      G * f - ∑ i : Fin d, pderiv i f * g i ∈ J ^ 2)
    (h q : ℕ) (hq : 2 * h < q) (hc : c ≤ q - h) (a : Fin d → R)
    (hG : aeval a G = t ^ h)
    (ha : ∀ f : MvPolynomial (Fin d) R, f ∈ J → t ^ q ∣ aeval a f) :
    ∃ a' : Fin d → R, (∀ i : Fin d, t ^ (q - h) ∣ a' i - a i) ∧
      ∀ f : MvPolynomial (Fin d) R, f ∈ J → t ^ (2 * (q - h)) ∣ aeval a' f := by
  sorry

end MvPolynomial
