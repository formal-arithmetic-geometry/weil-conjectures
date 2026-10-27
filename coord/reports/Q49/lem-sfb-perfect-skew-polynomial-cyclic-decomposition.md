## Worker report

Item: `lem-sfb-perfect-skew-polynomial-cyclic-decomposition`.
Module: `Sheaf.RingTheory.PerfectSkewPolynomialCyclicDecomposition`.
Declaration: `SkewPolynomial.exists_frobenius_cyclic_decomposition`.
The sole theorem has proof `sorry`. There are no new definitions, additional theorems,
new nodes, dependency repairs, or changes to the mathematical statement.

Source checked directly: `literature/milne-algebraic-groups_iAG2017.pdf`, PDF pages
308–309, printed pages 296–297: both division algorithms, Proposition 14.50,
Proposition 14.51 and the cyclic decomposition actually used in Proposition 14.52.
The node already removes the printed erroneous irreducibility restriction. The Lean
follows that corrected node; it makes no further correction and asserts no torsion-free
or irreducibility clause. No STATEMENT-DISPUTED issue remains.

### Hypotheses and conclusion, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| Characteristic p > 0 | `(p : ℕ) [CharP k p] (hp : 0 < p)` |
| sigma(c) = c^p | `[MulSemiringAction (Multiplicative ℕ) k]` and `hF : ∀ c : k, SkewPolynomial.φ c = c ^ p` specify exactly this endomorphism in Mathlib's existing interface |
| A is finite sums of c_i F^i | `SkewPolynomial k`, the existing finitely supported skew monoid algebra on `Multiplicative ℕ` |
| Coefficientwise addition | The existing additive structure of `SkewPolynomial k` |
| (c F^i)(b F^j) = c b^(p^i) F^(i+j) | The existing ring instance and `SkewPolynomial.monomial_mul_monomial`, with `hF` and `φ_iterate_apply` |
| Every element is a p-th power | `hperfect : ∀ c : k, ∃ b : k, b ^ p = c` |
| Every finitely generated left A-module M | `(M : Type v) [AddCommGroup M] [Module (SkewPolynomial k) M] [Module.Finite (SkewPolynomial k) M]` |
| Some integer q >= 0 | `∃ (q : ℕ)`; natural numbers include zero |
| Elements g_1,...,g_q in A | `(g : Fin q → SkewPolynomial k)` |
| A left A-module isomorphism | `Nonempty (M ≃ₗ[SkewPolynomial k] ...)` |
| Finite module direct sum | `⨁ i : Fin q, ...`, Mathlib's actual `DirectSum` with its existing left-module instance |
| Quotient A / A g_i | `SkewPolynomial k ⧸ Submodule.span (SkewPolynomial k) {g i}` |
| A g_i = {a g_i : a in A} | The singleton span in the left regular module; `Submodule.mem_span_singleton` identifies its elements with `a • g i = a * g i` |
| Quotient is a left-module quotient | The denominator is a `Submodule A A`; `Submodule.Quotient.module` supplies the left module, with no ring quotient or two-sidedness premise |
| g_i = 0 allowed | No condition is placed on `g`; its zero value is available |
| No irreducibility condition | No `Irreducible`, primality, nonzero, torsion or other restriction on the relations |

The action binder is the standard representation parameter required by Mathlib's
`SkewPolynomial` API, not an additional mathematical assumption on k or M. Its generator
is completely fixed by `hF`; `SkewPolynomial.φ_iterate_apply` determines every other
acting element. Conversely, for every field in the statement, the action
`(Multiplicative.ofAdd n) • c = c ^ (p ^ n)` exists: characteristic p makes p prime,
the p-th power map is a ring endomorphism, and its iterates are semiring endomorphisms.
Thus the binder plus `hF` encodes the ring defined in the node, rather than assuming
an unrelated twist or allowing a smaller class of fields. It does not assume a
canonical choice of p-th roots, which is unnecessary for stating the ring.

### Dependency declarations and source interfaces read

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, including its complete
  signature and docstring. Its `mathlib_match` is the list `["Field"]`, so no
  dependency-node Lean repair is required.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`; read the class and its `fg_top` field.
  It is exactly finite generation of the top submodule, including noncommutative rings.
- Existing ring: `SkewPolynomial`, its `instRing`, generator `φ`,
  `φ_iterate_apply`, and `monomial_mul_monomial`,
  `Mathlib.Algebra.SkewPolynomial.Basic`. Read the source introduction explaining
  how the `Multiplicative ℕ` action specifies the endomorphism.
- Quotients and sums: `Submodule.span`, `Submodule.mem_span_singleton`
  (`Mathlib.LinearAlgebra.Span.Defs`); quotient construction and left-module
  structure (`Mathlib.LinearAlgebra.Quotient.Defs`); `DirectSum` and its module
  instance (`Mathlib.Algebra.DirectSum.Module`). None requires commutative A.
- Recorded proof dependency: `SkewPolynomial.exists_two_sided_division`,
  `Sheaf.RingTheory.SkewPolynomialTwoSidedDivision`; read the full signature and
  proof-plan docstring and import it privately.
- Mathlib proof dependency `lem-sfb-left-principal-finite-submodules`: its
  recorded `mathlib_match` is `IsNoetherian.noetherian`, with the intermediate
  `PrincipalIdealRing.isNoetherianRing` and finite-module Noetherian instance.
  Read the source class/field and principal-ideal instance; import
  `Mathlib.RingTheory.PrincipalIdealDomain` and `Mathlib.RingTheory.Noetherian.Basic`
  privately for that proof route.
- `lem-sfb-two-sided-division-matrix-diagonalization` has neither a Lean record
  nor a Mathlib match on the read base. It is only a proof dependency: its
  mathematical step is fully preserved in the theorem docstring; there is no
  declaration or module to import yet. No new prerequisite is needed to type
  this statement. The maintainer can add its private import when stated.

### Edge cases checked before writing

- Zero module and no generators: `q = 0` is legal; `Fin 0` and the empty direct
  sum are available. No nontriviality assumption on M is made.
- A free cyclic factor uses `g i = 0`; its singleton span is the zero submodule,
  and its quotient is A. Free finite modules are therefore included.
- A unit relation generates all of A and gives a zero quotient; such trivial
  factors are allowed as in the node.
- Repeated or reducible relations, including powers of F, are unrestricted.
- k is a field, so characteristic p with `0 < p` automatically excludes p = 1
  and forces p prime. No separate, stronger prime or algebraic-closure premise
  was added. Characteristic zero is excluded exactly as in the node.
- Arbitrary perfect fields are covered, including nontrivial Frobenius: the
  statement assumes no finite-field condition and no commutativity of A.
- Independent explicit universes `u v` allow a module carrier in any universe;
  linear equivalence supports those different universes. No universe equality
  or extra smallness assumption is imposed.

### Searches made

All launcher searches used `msearch.py Q49
lem-sfb-perfect-skew-polynomial-cyclic-decomposition`:

1. `leanfinder`, query: "Every finitely generated left module over the Frobenius
   skew polynomial ring over a perfect field is a finite direct sum of cyclic
   quotients". Eight hits: commutative PID decomposition, finite-dimensional
   tower lemmas, finite Frobenius quotients and isocrystal results; no match.
2. `loogle`, query: `"SkewPolynomial"`. Twelve hits including `SkewPolynomial`,
   `SkewPolynomial.φ`, `instRing`, coefficients and basic operations; no
   cyclic-decomposition theorem. The existing ring is reused.
3. `grep`, query: `SkewPolynomial|Frobenius.*Action|frobenius.*Action`.
   Twelve hits in skew-polynomial basics and Witt-vector Frobenius files;
   no matching theorem.
4. `leansearch`, query: "Every finitely generated left module over a skew
   polynomial ring is a finite direct sum of cyclic modules". Eight hits:
   commutative PID decomposition, `ModuleCat.isFG`, finite direct sums,
   `SkewPolynomial`, and semisimple-module results; no matching theorem.
5. Local `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
   `SkewPolynomial|skew.polynomial|frobenius.*[Aa]ction`. Found the already
   recorded division lemma and the downstream additive-subgroup proof's
   citation of this item; no existing cyclic-decomposition declaration.
6. Local node-id search in `lean/WeilConjectures` found no occurrence.
   Name search for `exists_frobenius_cyclic_decomposition|frobenius_cyclic_decomposition`
   in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` found no existing declaration.

### Validation

`scompile.py Q49 lem-sfb-perfect-skew-polynomial-cyclic-decomposition` compiled
the delivered module cleanly, both sandbox and named-library passes. The first
probe caught that direct-sum notation needs `open scoped DirectSum`; this was
fixed using the existing global Mathlib notation. There are no file-local
notations, local instances, implicit universe variables, or auxiliary definitions.
The maximum Lean line length is 86 characters. Only the item's `lean` field
is changed in the node copy.

## Second reading by Q49

This is the dispatched worker's explicit self-check, not a claim of independent
review by a second agent. The dispatcher forbids starting other agents and assigns
the independent delivery review to the maintainer.

I re-read the node and completed module together. The field, positive
characteristic, specified Frobenius twist, p-th-power surjectivity and finite
left-module hypothesis each appear in the theorem. The conclusion contains
exactly a natural number q, q unrestricted ring elements and a left-linear
isomorphism to their finite direct sum of left-module quotients. In particular,
`Submodule.span A {g i}` uses left multiples, so it does not accidentally
assert a quotient-ring structure or switch to right ideals. `Fin q` permits
zero, and no g_i is required to be nonzero or irreducible. The only repair
needed during this reading/compilation was opening the existing direct-sum
notation scope; the mathematical statement was unchanged. The full five-step
DAG proof, including row-coordinate multiplication by V and both empty and
free-factor cases, is present in the theorem docstring. No new-node or
dependency-module interfaces are hidden in this delivery.
