module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.Finite
import Sheaf.TraceFormula.PolynomialShearLeadingCoefficient

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open MvPolynomial

namespace Algebra

/-- Refined Noether normalization at a prime.

Source: Stacks Project, Algebra, Lemma Tag 051P (lemma-refined-Noether-normalization),
statement and induction proof (blueprint: lem-trf-refined-noether-normalization-prime).

Proof plan, following the nine steps of Tag 051P. (1) Induct on `n`, using the
localization description of residue fields; the zero prime is handled by the original
variables, which are algebraically independent, and the case `n = 0` is included.
(2) For a nonzero prime choose a nonconstant element and apply the polynomial shear
lemma, obtaining a monic positive-degree equation in the last variable after a triangular
automorphism. (3) Evaluate the last source variable at that monic polynomial; the
resulting algebra map is finite by the integral-generator lemma. (4) Its contracted
prime is `p C + (y_n)` by polynomial coefficient expansion. (5) The residue field
extension over the contraction is finite, hence algebraic, so the transcendence-degree
tower formula preserves the degree. (6) Apply induction to the contraction and extend
the resulting finite map by the last variable. (7) Reduction modulo `y_n` computes the
new contraction as the coordinate ideal. (8) Compose the finite maps and undo the
shear; transitivity of finite modules proves finiteness. (9) The resulting contraction
is the required coordinate ideal, after renaming the variables.
-/
theorem refinedNoetherNormalizationPrime
    (k : Type u) [Field k] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    ∃ r : ℕ,
      Algebra.trdeg k q.ResidueField = (r : Cardinal) ∧
        r ≤ n ∧
        ∃ φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
          φ.toRingHom.Finite ∧
            Ideal.comap φ.toRingHom q =
              Ideal.span (Set.range (fun i : Fin n =>
                if r ≤ i.1 then MvPolynomial.X i else 0)) := by
  sorry

end Algebra
