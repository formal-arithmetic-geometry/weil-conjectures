module

public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Gluing divided powers on two ideals

Source: Stacks Project, Divided Power Algebra, Tag 07GQ (lemma-two-ideals), including
its displayed gluing formula (blueprint: lem-sfb-pd-glue-ideals).
-/

@[expose] public section

universe u

namespace DividedPowers

/-- Divided powers agree on the product of their ideals and glue uniquely on the sum if

they agree on the intersection. The glued operations satisfy the convolution formula,
including degree zero. Source: Stacks Project, Tag 07GQ (lemma-two-ideals).
(blueprint: lem-sfb-pd-glue-ideals)

Proof:
1. For either structure, scalar compatibility at scalar zero gives the vanishing of every
   positive operation at zero. The product axiom gives `x * g (r-1) x = r * g r x`.
   Induction then gives `r! * g r x = x^r`, without cancelling integers; this is Tag 07GM(1).
2. For `a ∈ U`, `b ∈ V`, scalar compatibility and the factorial identity give
   `ρ n (a*b) = b^n * ρ n a = n! * σ n b * ρ n a = σ n b * a^n = σ n (a*b)`.
   Induct over finite sums of products, simultaneously in all degrees, using the addition
   axiom term by term. The empty sum follows from step 1 and the fixed zeroth operation.
3. Assuming agreement on the intersection, define the operation at `a+b` by the displayed
   convolution. For a second decomposition `a'+b'`, put `w = a-a' = b'-b ∈ U ⊓ V`.
   Expand `ρ i (a'+w)` by addition, replace every `ρ j w` with `σ j w`, and regroup by
   addition for `σ`. This gives the convolution for `a'+b'`, proving well-definedness.
   In positive degree every term has a positive index on a factor, so lies in `U ⊔ V`.
4. Setting either summand to zero gives restriction to each ideal. Degree one is the
   identity. For scalar compatibility use the decomposition `c*a+c*b` and factor `c^n`
   out of the convolution. The degree-zero identities follow from the convention of one.
5. Expand the convolution for `(a+b)+(a'+b')` twice. Regroup the four-index finite sum by
   the total degree of the factors at `a,b`; commutativity gives the addition axiom.
6. Apply lem-sfb-pd-check-generators (Stacks Tag 07GP) to the generating set `U ∪ V`
   of `U ⊔ V`. Steps 3–5 give the range, identity, scalar and addition axioms everywhere.
   On `U` and `V`, multiplication and iteration reduce to those for the original structure:
   its positive operations remain in that ideal, so restriction also applies to iteration.
7. Every other extension has the same convolution by its addition axiom and restrictions.
   Every element of the sum has such a decomposition; positive operations therefore agree,
   and degree zero is fixed. Off the ideal both total extensions are zero. Thus the
   divided-power structures are equal, establishing uniqueness and the stated formula.
-/
theorem coincide_mul_and_existsUnique_sup {A : Type u} [CommRing A] (U V : Ideal A)
    (ρ : DividedPowers U) (σ : DividedPowers V) :
    (∀ (w : A), w ∈ U * V → ∀ (n : ℕ), 1 ≤ n → ρ.dpow n w = σ.dpow n w) ∧
      ((∀ (w : A), w ∈ U ⊓ V → ∀ (n : ℕ), 1 ≤ n → ρ.dpow n w = σ.dpow n w) →
        ∃! τ : DividedPowers (U ⊔ V),
          (∀ (a : A), a ∈ U → ∀ (n : ℕ), 1 ≤ n → τ.dpow n a = ρ.dpow n a) ∧
          (∀ (b : A), b ∈ V → ∀ (n : ℕ), 1 ≤ n → τ.dpow n b = σ.dpow n b) ∧
          (∀ (a b : A), a ∈ U → b ∈ V → ∀ (n : ℕ),
            τ.dpow n (a + b) =
              ∑ i ∈ Finset.range (n + 1), ρ.dpow i a * σ.dpow (n - i) b)) := by
  sorry

end DividedPowers
