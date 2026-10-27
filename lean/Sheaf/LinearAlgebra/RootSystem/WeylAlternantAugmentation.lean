module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Augmentation of a quotient of Weyl alternants

Source: Milne, Algebraic Groups (2017), Section 22d, p.480, antisymmetry operator before
Theorem 22.50, and Appendix C.15, C.18--C.22, pp.611--612. The formal-exponential
augmentation calculation is the agent-supplied argument recorded in the DAG
(blueprint: lem-sfb-weyl-alternant-augmentation).

The alternants and augmentation are expanded using `AddMonoidAlgebra.single` and the sum
of coefficients. Rational spanning is expressed by the equivalent assertion that a nonzero
integer multiple of every lattice vector belongs to the integer span of the roots/coroots.
The integer determinant used below agrees with the determinant on rational scalar extension.
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace RootPairing

open Classical in
/-- Augmentation of any polynomial quotient of two Weyl alternants, and positivity of the
integral half-sum of positive roots. Source: Milne, Algebraic Groups (2017), Section 22d,
p.480 and Appendix C.15, C.18--C.22, pp.611--612
(blueprint: lem-sfb-weyl-alternant-augmentation).

Proof plan from the node, including its agent-supplied augmentation calculation:

1. In rank zero both lattices vanish, the Weyl group is trivial, both alternants are one,
and the polynomial identity forces `q = 1`. The product is empty and positivity is vacuous.
Otherwise pass to the rational vector spaces. Put `N` equal to the number of positive roots,
`D(v)` equal to the product of positive coroot evaluations, and `B(h)` equal to the product
of positive root evaluations on the dual space; regard these as homogeneous polynomials.
2. A simple reflection permutes the positive roots other than its simple root: another
positive root has a positive coordinate away from that simple root, which reflection leaves
unchanged. Summing proves that the half-sum pairs to one with every simple coroot.
3. Average a rational positive definite form over the finite Weyl group. Reflection
invariance gives the coroot formula `2 b(v, alpha) / b(alpha, alpha)`. The preceding step
makes its value on the half-sum and each simple root positive. Positive-root coordinates
therefore imply positivity for every positive coroot. Integrality follows from the lattice
pairing. The same formula and reducedness show the factors of `D` are nonproportional.
4. Each root reflection multiplies `B` by a sign. Factor out its own root linear factor
and restrict the remaining factors to its fixed hyperplane. They remain nonzero and their
product is nonzero in the polynomial domain (`lem-sfb-polynomial-field-ufd`), including the
zero-dimensional hyperplane. Cancellation forces the sign to be minus one. Thus every Weyl
element acts on `B` by its determinant.
5. Take a generic dual vector over a rational function field, so `B(h)` is nonzero. The
homogeneous degree-`j` polynomial `F_j(v) = sum_w det(w) <wv,h>^j / j!` is alternating and
vanishes on every root-reflection hyperplane. Distinct-hyperplane divisibility
(`lem-sfb-distinct-hyperplane-polynomial-divisibility`) gives `F_j = 0` below degree `N`
and `F_N = c D` at degree `N`.
6. Apply the product of the positive-root directional derivatives to `F_N`. The factorial
cancels, and the sign calculation gives `|W| B(h)`, which is nonzero. Hence `c` is nonzero.
7. Send the group-algebra basis vector at `x` to the formal exponential of `<x,h> t`.
The binomial formula proves multiplicativity, also for negative lattice vectors. Its
constant coefficient on `q` is augmentation and its degree-`j` coefficient on the alternant
at `lambda` is `F_j(lambda)`.
8. Apply this map to the polynomial identity and compare degree `N`. Lower degrees vanish,
leaving `augmentation(q) c D(sigma) = c D(nu)`. Regularity of `sigma` and the nonvanishing
of `c` allow cancellation. Injectivity of the rational field map gives the displayed
rational product, including singular `nu`. Together with steps 1 and 3 this is the claim. -/
theorem weylAlternant_augmentation
    {ι : Type u} [Fintype ι]
    {X : Type v} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {Y : Type w} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsReduced]
    (hroot : ∀ x : X, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ (Set.range P.root))
    (hcoroot : ∀ y : Y, ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ Submodule.span ℤ (Set.range P.coroot))
    (b : P.Base) (ρ : X)
    (hρ : (2 : ℤ) • ρ = ∑ i ∈ Finset.univ.filter b.IsPos, P.root i)
    [Fintype P.weylGroup] (ν σ : X)
    (hσ : ∀ i : ι, P.toLinearMap σ (P.coroot i) ≠ 0)
    (q : AddMonoidAlgebra ℚ X)
    (hq : q * (∑ g : P.weylGroup, AddMonoidAlgebra.single (g • σ)
        ((LinearMap.det (P.weylGroupRootRep g) : ℤ) : ℚ)) =
      ∑ g : P.weylGroup, AddMonoidAlgebra.single (g • ν)
        ((LinearMap.det (P.weylGroupRootRep g) : ℤ) : ℚ)) :
    q.coeff.sum (fun _ a ↦ a) =
        ∏ i ∈ Finset.univ.filter b.IsPos,
          (P.toLinearMap ν (P.coroot i) : ℚ) / (P.toLinearMap σ (P.coroot i) : ℚ) ∧
      ∀ i : ι, b.IsPos i → 0 < P.toLinearMap ρ (P.coroot i) := by
  sorry

end RootPairing
