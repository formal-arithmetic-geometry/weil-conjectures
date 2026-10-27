module

public import Sheaf.RingTheory.DividedPowerDGA
import Sheaf.RingTheory.PDDerivationCompatibilityClosure

/-!
# Odd derivations on free graded divided-power algebras

Source: Stacks Project, `dpa.tex`, Tag 09PS, proof, first paragraph and its
one-variable-at-a-time hint (blueprint: lem-sfb-free-graded-pd-odd-derivations).

The operator lowers degree by one and is not required to square to zero.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace GradedAlgebra

/-- Arbitrary degree-minus-one values on the specified free generators extend uniquely
as an S-linear signed derivation compatible with divided powers of positive even
homogeneous elements. There is no differential or square-zero assumption.
Source: Stacks, 09PS, proof, omitted operator construction (1),(2), with 09PH,
09PI, 0F4I and 09PG (blueprint: lem-sfb-free-graded-pd-odd-derivations).

Proof:
1. Use `def-sfb-divided-power-dga` and the normal forms of
`lem-sfb-divided-power-variable-adjunction`. Order each finite positive-degree
label set and re-adjoin the generators in increasing degree, obtaining P'. Both
P and P' are free over S[J₀] on the same standard monomials: odd exponents are
zero or one, while an even generator contributes its divided symbols T^[m].
Map a monomial of P' to the corresponding ordered product in P. Reordering
changes only a sign. The strict sign rules, odd squares zero, and binomial
multiplication of divided symbols show that this is a graded algebra isomorphism
φ fixing every generator and divided symbol. Full divided-power preservation
of φ is not needed. The subalgebra on generators of degree below e contains
P'_(e-1), so the assigned value of the next degree-e generator is already there.
Start with the zero operator on S[J₀].
2. At a single adjunction define on homogeneous a of degree p
D(a T^[m]) = D(a) T^[m] + (-1)^p a v T^[m-1] for m > 0, and keep D(a)
for m = 0. For odd T only m = 1 occurs. Extend S-linearly using the actual
free-module coordinates from `lem-sfb-divided-power-variable-adjunction`.
Both terms have degree p+me-1 and the value on T is v.
3. For even e, multiply a T^[m] and b T^[n] using the binomial coefficient.
The old derivative terms agree by induction. Move the odd element v past b
using `def-sfb-nonnegative-strict-graded-algebra`. The remaining coefficients
are choose(m+n-1,m-1) and choose(m+n-1,m), whose sum is choose(m+n,m).
If an exponent is zero, omit its derivative term. Bilinearity proves Leibniz.
4. For odd e, v is even. Check products of the four module types a,b and aT,bT.
The old and mixed products follow by the sign rule and the inductive Leibniz
rule. The product of two T terms is zero. Its two Leibniz terms not containing
T² have coefficients (-1)^p and (-1)^(p+1), so cancel. All remaining terms
contain T². This uses strict odd-square vanishing and works in characteristic two.
5. Iterate these extensions. By the union clause of
`lem-sfb-divided-power-variable-adjunction`, every element occurs in a completed
degree stage, and successive operators agree on overlaps. Their union D' is
linear, lowers degree and satisfies signed Leibniz. Transport it to P by φ.
The formula gives D(γ_m(T)) = v_T γ_(m-1)(T) for every positive even generator,
since φ fixes its divided symbols. Degree-zero generator values are zero.
6. Apply `lem-sfb-pd-derivation-compatibility-closure` to this operator on P.
Its compatibility locus contains each even generator and all its divided powers.
An even monomial with no odd generators is an even multiple of one such divided
power. An even monomial containing odd generators has a positive even number of
them, and factors as a product of two homogeneous odd elements. Thus all positive
even monomials belong to the locus. Their normal forms span each positive even
component over P₀; closure under sums and even multiplication gives compatibility.
7. Transport a competing operator to P'. It is zero on degree zero, has the
prescribed values on odd generators, and compatibility forces its values on each
divided symbol of an even generator. Leibniz forces the formula of step 2 on
each normal form. Induction and the union give equality everywhere. Neither
D(v_T) nor D² is used. -/
theorem existsUnique_freeGradedPDOddDerivation
    {S : Type u} {P : Type v} [CommRing S] [Ring P] [Algebra S P]
    (𝒜 : ℕ → Submodule S P) [GradedAlgebra 𝒜] [IsStrictlyGradedCommutative 𝒜]
    (γ : GradedDividedPowers 𝒜) (J : ℕ → Type w) [∀ e : ℕ, Finite (J e)]
    (generator : ∀ e : ℕ, J e → P)
    (hpolynomial : Nonempty (γ.PolynomialPresentation J generator))
    (values : ∀ e : ℕ, J e → integerComponent 𝒜 ((e : ℤ) - 1)) :
    ∃! δ : P →ₗ[S] P,
      (∀ (i : ℕ) (x : P), x ∈ 𝒜 i → δ x ∈ integerComponent 𝒜 ((i : ℤ) - 1)) ∧
      (∀ (e : ℕ) (j : J e), δ (generator e j) = (values e j : P)) ∧
      (∀ (i j : ℕ) (x y : P), x ∈ 𝒜 i → y ∈ 𝒜 j →
        δ (x * y) = δ x * y + (-1 : P) ^ i * (x * δ y)) ∧
      (∀ (i n : ℕ) (x : evenSubalgebra 𝒜), 0 < i → 0 < n →
        (x : P) ∈ 𝒜 (2 * i) →
          δ (γ.dpow n x : P) = δ (x : P) * (γ.dpow (n - 1) x : P)) := by
  sorry

end GradedAlgebra
