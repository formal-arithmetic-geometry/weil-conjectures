module

public import Sheaf.RingTheory.NonnegativeStrictGradedAlgebra
public import Sheaf.RingTheory.GradedDividedPowers

/-!
# Propagation of divided-power compatibility for an odd derivation

Source: Stacks Project, Tags 09PF and 09PG, axioms (3)--(7), supporting the
operator-extension argument in Tag 09PS, proof (1), (2).
(blueprint: lem-sfb-pd-derivation-compatibility-closure)

The compatibility locus is a subset of the even subalgebra with its actual
inherited operations; its definition also requires positive degree.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace GradedAlgebra

/-- The positive even elements on which an operator obeys the divided-power rule.
Source: Stacks Project, Tag 09PS, proof (2), with the divided powers of Tag 09PG.
(blueprint: lem-sfb-pd-derivation-compatibility-closure). -/
def pdDerivationCompatibilityLocus {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedCommutative 𝒜]
    (γ : GradedDividedPowers 𝒜) (D : A →ₗ[R] A) : Set (evenSubalgebra 𝒜) :=
  {x | x ∈ positiveEvenIdeal 𝒜 ∧ ∀ (n : ℕ), 0 < n →
    D (γ.dpow n x : A) = D (x : A) * (γ.dpow (n - 1) x : A)}

/-- Divided-power compatibility of a degree minus one signed derivation propagates
under addition, even multiplication and positive divided powers, and holds on
products of homogeneous odd elements. Neither freeness nor `D ∘ D = 0` is assumed.
Source: Stacks Project, Tag 09PG, axioms (3)--(7); auxiliary calculus for the omitted
operator-extension argument of Tag 09PS, proof (1), (2).
(blueprint: lem-sfb-pd-derivation-compatibility-closure).

Proof: Use `def-sfb-nonnegative-strict-graded-algebra` to expand finite homogeneous
sums: even elements commute with all elements, and D sends even degrees to odd
degrees. Since the negative components vanish, D(1) = 0. The scalar axiom of
`def-sfb-graded-divided-power-structure` gives γ_n(0) = 0 for n > 0, proving the
zero assertion. The n = 1 compatibility equation is the identity D(x) = D(x)1.
Differentiate the divided-power addition formula. Its two endpoint derivatives
of γ_0 vanish; the two remaining sums reindex to γ_(n-1)(x+y), proving addition.
For even a, induction with the even Leibniz rule gives D(a^n) = n a^(n-1)D(a).
Differentiate γ_n(ax) = a^n γ_n(x) and use x γ_(n-1)(x) = n γ_n(x), obtained
from the product axiom for n > 1. This proves even multiplication, with no
requirement that D(a) vanish, including for nonhomogeneous a.
For iteration put z = γ_m(x). For m,n > 1, differentiating the iteration axiom
gives c D(x) γ_(nm-1)(x), where c = (nm)!/(n!(m!)^n). The other side is
b binom(nm-1,m-1) D(x) γ_(nm-1)(x), where
b = ((n-1)m)!/((n-1)!(m!)^(n-1)). These integer coefficients are equal: expand
the factorials to obtain (nm-1)!/((n-1)!(m-1)!(m!)^(n-1)) on both sides.
No integer is cancelled in A. The cases m = 1 or n = 1 are immediate.
Finally for homogeneous odd u,v, put w = uv. Higher divided powers of w vanish
by the odd-product axiom. For n > 2 this gives both sides zero. For n = 2,
D(w)w = (D(u)v-uD(v))uv = 0: D(u), D(v) are even, vu = -uv and u² = v² = 0.
The last two facts are the independent strict-commutativity axioms, so the argument
also applies in characteristic two. The grading places uv in the positive even
part. These five calculations use precisely the two cited definition nodes. -/
theorem pdDerivationCompatibilityLocus_closure {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedCommutative 𝒜]
    (γ : GradedDividedPowers 𝒜) (D : A →ₗ[R] A)
    (hdegree : ∀ (i : ℕ) (x : A), x ∈ 𝒜 i →
      D x ∈ integerComponent 𝒜 ((i : ℤ) - 1))
    (hleibniz : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : A) ^ i * (x * D y)) :
    (0 : evenSubalgebra 𝒜) ∈ pdDerivationCompatibilityLocus 𝒜 γ D ∧
    (∀ (x y : evenSubalgebra 𝒜), x ∈ pdDerivationCompatibilityLocus 𝒜 γ D →
      y ∈ pdDerivationCompatibilityLocus 𝒜 γ D →
      x + y ∈ pdDerivationCompatibilityLocus 𝒜 γ D) ∧
    (∀ (a x : evenSubalgebra 𝒜), x ∈ pdDerivationCompatibilityLocus 𝒜 γ D →
      a * x ∈ pdDerivationCompatibilityLocus 𝒜 γ D) ∧
    (∀ (m : ℕ), 0 < m → ∀ (x : evenSubalgebra 𝒜),
      x ∈ pdDerivationCompatibilityLocus 𝒜 γ D →
      γ.dpow m x ∈ pdDerivationCompatibilityLocus 𝒜 γ D) ∧
    (∀ (i j : ℕ) (u v : A), u ∈ 𝒜 (2 * i + 1) → v ∈ 𝒜 (2 * j + 1) →
      ∃ z : evenSubalgebra 𝒜, (z : A) = u * v ∧
        z ∈ pdDerivationCompatibilityLocus 𝒜 γ D) := by
  sorry

end GradedAlgebra
