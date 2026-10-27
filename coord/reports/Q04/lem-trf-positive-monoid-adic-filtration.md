## Worker report

Item: `lem-trf-positive-monoid-adic-filtration`, group Q04, 2026-10-24 UTC.
Module: `Sheaf.RingTheory.PositiveMonoidAdicFiltration`.
Declaration: `AddMonoidAlgebra.positiveMonoid_adic_filtration`.
The single theorem has `by sorry`; no definitions or proofs are added.
The item's only changed field is `lean`; its signature is copied verbatim from
`theorem` through the conclusion, before `:=`.

Read the whole item, its six proof steps, its sole statement/proof dependency,
and the full dependency module. Read ILO Exposé VI §1.6(i)--(ii), printed p. 70
(PDF p. 76), with `pdftotext -f 76 -l 76 ... -`. That page supplies the motivating
completed monoid models, not this coefficient theorem, as the node explicitly
says. Also read the current blueprint ancestor `lem-trf-local-term-locality` in
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
No statement correction or disputed clause was found.

Clause-by-clause correspondence:

- An abelian group is `(G : Type u) [AddCommGroup G]`; its additive submonoid is
  `(P : AddSubmonoid G)`. Inclusion is the actual subtype coercion `p : G`.
  Finite generation is `(hfg : P.FG)`, Mathlib's closure-of-finite-set notion.
  No free, finite-rank, saturated, or ambient finite-generation assumption is added.
- The integral homomorphism is `(wgt : G →+ ℤ)`. Strict positivity is exactly
  `(hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G))`.
- Nonnegative integer lengths are `q : ℕ`. The set `L(p)` is written inline as
  `{q : ℕ | ∃ f : Fin q → P, (∀ i : Fin q, f i ≠ 0) ∧ (∑ i, f i) = p}`.
  This includes the empty sum for `q = 0`.
- `∃ ν : P → ℕ` introduces all the largest lengths simultaneously, independently
  of the coefficient ring. `∀ p, IsGreatest ... (ν p)` asserts both attainment and
  maximality; it does not merely bound all lengths or choose arbitrary lengths.
- The next three conjuncts are `ν 0 = 0`,
  `∀ p, (ν p : ℤ) ≤ wgt (p : G)`, and
  `∀ a b, ν a + ν b ≤ ν (a + b)`.
- Bounded-weight finiteness is
  `∀ M : ℤ, 0 ≤ M → Set.Finite {p : P | wgt (p : G) ≤ M}`.
  Here `M` is literally an integer as in the node.
- For every `p : P` and `k : ℕ` with `1 ≤ k`,
  `Set.Finite {f : Fin k → P | (∑ i, f i) = p}` is precisely finiteness of
  ordered `k`-tuples; zero summands are allowed in this clause.
- For every `n : ℕ` with `1 ≤ n`,
  `Set.Finite {p : P | ν p < n}` is the stated finiteness of `S_n`.
- The ring quantifier is `∀ (A : Type v) [CommRing A] (I : Ideal A)`, with a
  universe independent of `G`. Locality, completeness and Noetherianity are absent.
  `F : AddMonoidAlgebra A P` is the finite-sum monoid algebra from the dependency's
  zero-variable model, and `F.coeff p` is exactly `c_p`.
- The ideal `J` is written inline using `Ideal.span` of the union of the sets
  `{f | ∃ a : A, a ∈ I ∧ f = single 0 a}` and
  `{f | ∃ p : P, p ≠ 0 ∧ f = single p (1 : A)}`.
  These are exactly the coefficient and nonzero monomial generators. This is
  neither a completed ideal nor a closure in a topology.
- For every `n ≥ 1` and every `F`, the final equivalence states membership in
  this ideal's `n`th power iff `∀ p : P, F.coeff p ∈ I ^ (n - ν p)`.
  Natural subtraction gives `max(n - ν(p), 0)` and Mathlib's ideal power gives
  the empty-product convention `I ^ 0 = ⊤`. All exponents are quantified, not
  only those in the finite support of `F`.

Dependency declarations and reuse:

- `def-trf-complete-toric-model` records `Sheaf.RingTheory.CompleteToricModel`,
  `ToricMonoid.IsCompleteModel`, and its auxiliary declarations. The full source
  and docstrings were read. The part used here is `ToricMonoid.PolynomialRing`,
  defined as `MvPolynomial (Fin n) (AddMonoidAlgebra L P)`. With zero polynomial
  variables the coefficient ring is exactly the node's stated finite-sum algebra
  `AddMonoidAlgebra A P`; the statement uses that Mathlib ring directly, without
  introducing a second monoid algebra. `IsCompleteModel` is not a hypothesis of
  this node. The recorded module is a public import, satisfying the sole
  statement dependency (also the sole proof dependency).
- Mathlib `GroupTheory.Finiteness`: `AddSubmonoid.FG`, read its finite-closure
  definition. Mathlib `Algebra.MonoidAlgebra.Defs` and `.Basic` (reexported by the
  recorded dependency): `AddMonoidAlgebra`, `.single`, `.coeff`, and its ordinary
  convolution ring structure. Mathlib `RingTheory.Ideal.Operations`: `Ideal.span`
  and ordinary ideal powers. `IsGreatest`, `Set.Finite`, `Fin`, and finite sums
  are used directly. There is no missing notion requiring a new node.

Edge cases checked before writing and again against the final signature:

- `P = {0}` admits the empty generator set and the vacuous positive-weight
  condition. Only the empty nonzero decomposition of zero exists, so `ν 0 = 0`.
  All sublevel and tuple sets have at most one element. The filtration reduces
  to ordinary powers of `I` in `A`.
- In any `P`, a nonempty tuple of nonzero terms has positive weight, so it cannot
  sum to zero. The maximum-length assertion at zero therefore says the right thing.
- `M = 0` gives only exponent zero. `n = 1` gives `S_1 = {0}` and the ordinary
  generator criterion for `J`. `k = 1` is the singleton tuple with entry `p`.
- If `ν p ≥ n`, the required exponent is zero, so its coefficient is unrestricted.
  If `p = 0`, its coefficient must lie in `I ^ n`.
- `I = 0` gives the pure nonzero monomial ideal; `I = ⊤` gives the whole ring.
  The zero ring, coefficient zero, and exponents outside the support are included.
- No ordering or decidability hypothesis is imposed on `G` or `P`; classical
  elaboration only supplies ordinary implicit decidable equality instances.

Searches for an existing declaration, on 2026-10-24:

- `msearch.py ... leanfinder` query "Positive finitely generated additive monoid
  maximal decomposition length and mixed coefficient monomial ideal powers":
  eight hits, including `Polynomial.coeff_prod_mem_ideal_pow_tsub`,
  `Ideal.sum_pow_mem_span_pow`, and `mem_reesAlgebra_iff_support`. They concern
  univariate degree estimates or ordinary generators/Rees coefficients and do not
  state this positive-monoid theorem.
- `msearch.py ... loogle` query `AddMonoidAlgebra, Ideal`: one hit,
  `AddMonoidAlgebra.mem_ideal_span_of'_image`. Read its complete signature and
  docstring in Mathlib/Algebra/MonoidAlgebra/Ideal.lean. It characterizes support
  of pure monomial ideals, with no mixed coefficient powers or length finiteness.
- `msearch.py ... leansearch` query "Positive additive monoid maximal length of
  decompositions and coefficientwise characterization of mixed ideal powers":
  eight hits, including `AddMonoidAlgebra.grade.decomposition`,
  `Ideal.sup_pow_add_le_pow_sup_pow`, and degree lemmas. None is the statement.
- `msearch.py ... grep` query `decomposition|adic|span.*pow` in
  `Algebra/MonoidAlgebra`: five hits, generic grading and homomorphism
  decompositions, no coefficient filtration theorem.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for positive monoid/length/filtration terminology:
  found `PositiveMonoidConvolutionLength`, `MonoidCompletionCoefficients` and
  `FinitePatternFactorization`. Read all three modules. They impose additional
  lattice, local, or Noetherian hypotheses or address completed coefficient
  families. None states this theorem for an arbitrary ambient group and arbitrary
  coefficient ideal. The item is only mentioned in proof docstrings of consumers.
- `grep -rn 'lem-trf-positive-monoid-adic-filtration' lean/WeilConjectures`:
  no hits. Exact-name `rg` for `positiveMonoid_adic_filtration` and related
  filtration names over Mathlib, both project source trees and the upstream-name
  index: no collisions. All machine-search results are in sandbox `searches.jsonl`.

Validation: prescribed `scompile.py Q04 lem-trf-positive-monoid-adic-filtration
<module file>` passed both sandbox and library module modes with no errors or
warnings. All universes and variables are explicitly bound. Maximum Lean line
length is 88 characters. The theorem's docstring includes all six proof steps,
with the agent-origin/source distinction retained. Dry-run and push results are
recorded below after execution.

## Second reading by Q04

A separate second pass by the same worker reopened the final Lean signature and
the original JSON statement together; no independent worker was started because
the dispatcher's brief expressly forbids starting other agents. The maintainer
performs the independent delivery review.

The pass matched the actual subgroup inclusion and `P.FG`, the positive integer
weight, the attained maximum of nonzero `Fin q` decompositions, its zero value,
weight bound and superadditivity, the integer-weight sublevel sets, all ordered
positive-length tuple sets, and the length sublevel sets. It then checked the
union inside `Ideal.span` generator by generator and both sides of the final
coefficient equivalence. In particular, the last clause uses the same `ν` as
all preceding conjuncts, quantifies over every coefficient of every finite
polynomial and every commutative ring/ideal, and uses natural subtraction to
retain the unrestricted-coefficient case. The source ring is the dependency's
underlying finite-sum algebra with no polynomial variables. No hypothesis or
clause mismatch was found and no change was needed during this second pass.

Delivery validation: `deliver2.py Q04 lem-trf-positive-monoid-adic-filtration
--no-push` printed `OK (dry run): commit efcf16fc2ea passes the preflight and
compiles; nothing pushed`. The deliverable set was exactly this report, the item
node, and `lean/Sheaf/RingTheory/PositiveMonoidAdicFiltration.lean`. A final JSON
comparison confirmed that `lean` is the only changed field.
