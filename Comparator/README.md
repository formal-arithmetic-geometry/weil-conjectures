# Comparator challenge: the Weil conjectures

A [leanprover/comparator](https://github.com/leanprover/comparator) challenge/solution
pair for the headline result of this repository:

> Let `X` be a smooth, proper, geometrically integral scheme of dimension `d` over a
> finite field `k` with `q` elements and let `Z(X, t) = exp (∑ N_n t ^ n / n) ∈ ℚ⟦t⟧` be
> its zeta function, where `N_n = #X(𝔽_(q ^ n))`. Then
> `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` for polynomials `Pᵢ ∈ ℤ[t]` with
> `Pᵢ(0) = 1`, `P₀ = 1 - t` and `P_{2d} = 1 - qᵈ t`, such that `α ↦ qᵈ / α` matches the
> inverse roots of `Pᵢ` with those of `P_{2d - i}` (functional equation) and every inverse
> root of `Pᵢ` has absolute value `q^{i/2}` (Riemann hypothesis).

The challenge consists of two theorems:

- `WeilConjectures.zetaSeries_rational` — **rationality** (Dwork): for an arbitrary scheme
  of finite type over a finite field, `Z(X, t)` is a rational function with integer
  coefficients. No smoothness or properness is needed here.
- `WeilConjectures.weil_conjectures` — the **full Weil conjectures** (Dwork,
  Grothendieck, Deligne) in the smooth, proper, geometrically integral case: the
  factorization above, together with the functional equation and the Riemann hypothesis.

The three parts are packaged into the predicates `AlgebraicGeometry.IsWeilFactorization`,
`AlgebraicGeometry.WeilFunctionalEquation` and `AlgebraicGeometry.WeilRiemannHypothesis`,
stated in terms of the complex roots `z = 1 / α` of the `Pᵢ`: the Riemann hypothesis reads
`‖z‖ = q^{-i/2}`, and the functional equation says that `z ↦ 1 / (qᵈ z)` maps the root
multiset of `Pᵢ` to that of `P_{2d - i}`.

Weil's fourth conjecture — if `X` lifts to a smooth proper scheme over a number ring, then
`deg Pᵢ` is the `i`-th Betti number of the associated complex manifold — needs singular
cohomology of the analytification and is not part of the challenge.

- `Weil/Definitions.lean` — the definitions shared by challenge and solution, using **only
  mathlib** (`import Mathlib`): the model `FiniteField.galoisExtension k n` of the degree
  `n` extension of `k`, the rational points `AlgebraicGeometry.Scheme.Hom.fieldPoints`
  and point counts `AlgebraicGeometry.Scheme.Hom.pointCount` relative to a structure
  morphism `f : X ⟶ Spec k`, the zeta function
  `AlgebraicGeometry.Scheme.Hom.zetaSeries` itself, and the three predicates above.
- `Weil/Challenge.lean` — states the two theorems, with `sorry`.
- `Weil/Solution.lean` — proves the identical statements using this repository
  (`WeilConjectures/Statement.lean`).
- `config.json` — the comparator configuration.

To verify, build both modules and run comparator (see the comparator README for the
sandboxed invocation):

```bash
lake build Challenge Solution
lake env <path/to/comparator> Comparator/config.json
```
