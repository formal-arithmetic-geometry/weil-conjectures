## Worker report

The module `lean/Sheaf/RingTheory/BuchbergerStandardRepresentationCriterion.lean` states
`MonomialOrder.buchberger_standard_representation_criterion`, with proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement changes.
The complete six-step accepted DAG proof is rendered in the theorem docstring.

Source checked: [Yankı Lekili, Commutative Algebra, Lecture 7](https://lekili.duckdns.org/teaching/calg/lec07.html),
Theorem 4.11 converse and Lemma 4.12. The source treats finite generators and division
remainders; the node explicitly supplies the arbitrary-family strict-representation
adaptation. The delivered statement follows that accepted node verbatim in mathematical
content, including its empty-set case. It does not impose a division algorithm or a
finiteness assumption. The cited local lecture document is still absent; the primary
lecture page was opened and read online.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `k` is `{k : Type u} [Field k]`, with its coefficient universe explicitly
  declared. No restriction on characteristic is imposed.
- The number of variables `r ≥ 1` is `{r : ℕ} (hr : 1 ≤ r)`.
- The ring `k[x₁,…,xᵣ]` is `MvPolynomial (Fin r) k`. Relabeling its variables by
  `Fin r = {0,…,r-1}` changes no object or hypothesis.
- The total well-order on exponent vectors, zero least and preserved by addition,
  is `m : MonomialOrder (Fin r)`. Its `syn` has a linear order and well-founded
  strict relation, and `toSyn` is an additive equivalence monotone for the ordinary
  coordinatewise order. This monotonicity adds no assumption: a translation-preserving
  order with zero least is coordinatewise monotone, since coordinatewise `α ≤ β`
  gives `β = α + (β - α)`. Conversely the structure supplies exactly the required
  total additive well-order, with zero least (`MonomialOrder.orderBot`). Finitely
  supported exponent functions on the finite type `Fin r` are all vectors in ℕʳ.
- The greatest support exponent `LM(f)` is `m.degree f`; its coefficient `LC(f)`
  is `m.leadingCoeff f`. Their source definitions were read, including the convention
  `m.degree 0 = 0`. Strict comparisons always apply only to nonzero products here.
- An arbitrary set `B ⊆ S` is `B : Set (MvPolynomial (Fin r) k)`. It has no
  `Finite`, `Fintype`, `Nonempty`, or homogeneity requirement.
- Nonzero monic generators are `hB : ∀ b ∈ B, b ≠ 0 ∧ m.Monic b`.
  Mathlib's `m.Monic b` is defined by `m.leadingCoeff b = 1`, exactly the node's
  convention. The explicit nonzero conjunct retains the node's explicit condition.
- The vector `λ(b,c)` is `m.degree b ⊔ m.degree c` in the *coordinatewise* lattice
  on finitely supported exponent vectors, not the maximum for the monomial order.
- The difference `P(b,c)` is Mathlib's `m.sPolynomial b c`.
  `MonomialOrder.sPolynomial_def` writes it as
  `monomial (λ - m.degree b) (m.leadingCoeff c) * b -`
  `monomial (λ - m.degree c) (m.leadingCoeff b) * c`.
  Both coefficients equal 1 by `hB`, so this is precisely the node's specified
  difference. No alternative S-polynomial normalization changes the statement.
- The hypothesis is for every pair, including equal generators:
  `hS : ∀ b ∈ B, ∀ c ∈ B, ...`.
- The polynomials `qᵤ`, with only finitely many nonzero and indexed by members of `B`,
  are `q : B →₀ MvPolynomial (Fin r) k`. Here `B` as a type is its subtype of
  member polynomials; it remains valid for empty and infinite sets.
- The representation equality is
  `m.sPolynomial b c = q.sum (fun u a ↦ a * (u : MvPolynomial (Fin r) k))`.
  `Finsupp.sum` sums over the finite support of `q`, exactly the sum in the node.
  Since the summand at coefficient zero is zero, ignoring other indices changes nothing.
- Each nonzero product satisfies the required strict bound:
  `∀ u : B, q u * (u : MvPolynomial (Fin r) k) ≠ 0 →`
  `m.toSyn (m.degree (q u * (u : MvPolynomial (Fin r) k))) <`
  `m.toSyn (m.degree b ⊔ m.degree c)`.
  The comparison uses the monomial order through `toSyn`, whereas `⊔` remains the
  coordinatewise maximum defining λ. The guard is on the product, exactly as in the node.
- A nonzero member `f` of the generated ideal is
  `(f : MvPolynomial (Fin r) k) (hf : f ∈ Ideal.span B) (hf0 : f ≠ 0)`.
- The complete conclusion is
  `∃ b ∈ B, ∀ a : Fin r, m.degree b a ≤ m.degree f a`:
  one member `b` satisfies the inequality in every coordinate, not separate members
  for separate coordinates. There is no additional conclusion or hypothesis.
- The empty-set clause is retained by allowing arbitrary `B`; if `B = ∅`,
  `Ideal.span B = ⊥`, so `hf` and `hf0` are incompatible, as required.

Dependency declarations read and used:

- `def-weil-field` is a Mathlib leaf with `mathlib_match = ["Field"]` and no `lean`
  record. `Field`, in `Mathlib.Algebra.Field.Defs`, is used directly as `[Field k]`.
  Its full declaration and docstring were read; it extends `CommRing` and `DivisionRing`.
- `def-weil-pbc-mv-polynomial-ring` records `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`. Its abbreviation and docstring were read,
  as were `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` and
  `MvPolynomial.algHom_ext` in Basic, which provide the node's universal property.
  Only the ring itself occurs in this theorem. These modules are exposed transitively
  by the public import `Mathlib.RingTheory.MvPolynomial.MonomialOrder`.
- The proof dependency `lem-sfb-monomial-order-leading-product` is a Mathlib leaf
  recording `MonomialOrder.degree_mul` and `MonomialOrder.leadingCoeff_mul` in
  `Mathlib.RingTheory.MvPolynomial.MonomialOrder`. Their complete statements and
  docstrings were read (nonzero factors for degree, all factors for coefficient).
  The same module is already a public statement import; no duplicate import is needed.
- Existing auxiliary definitions, all reused: `MonomialOrder` in
  `Mathlib.Data.Finsupp.MonomialOrder`; `MonomialOrder.degree`, `leadingCoeff`,
  `Monic`, `sPolynomial`, and `sPolynomial_def` in
  `Mathlib.RingTheory.MvPolynomial.MonomialOrder`; `Ideal.span` in
  `Mathlib.RingTheory.Ideal.Span`; and the existing `Finsupp` finite-support sum.
  Both direct imports are used by the statement.

Edge cases checked before writing:

- `B = ∅`: the conclusion is vacuous for nonzero elements of the zero ideal;
  no nonempty subtype or finite enumeration of `B` is required.
- A constant generator: its monicity forces it to be 1. Its leading exponent is
  zero and divides every exponent. The theorem includes the unit ideal.
- `b = c` or an S-polynomial equal to zero: choose `q = 0`. Its sum is zero and
  every product guard is false, including when λ is zero. There is no demand `0 < 0`.
- Zero coefficient products in any representation are exempt from the strict bound.
  Zero generators are excluded just as in the node.
- `r = 1` is allowed; `r = 0` is excluded exactly by the node's stated `r ≥ 1`.
- Infinite `B` remains allowed because each pair gets its own finitely supported
  coefficient family. The proof uses finite expressions, not finiteness of `B`.
- Nonhomogeneous generators are allowed; no grading structure or homogeneity predicate
  appears. For example under `x > y`, `B = {x+y,x}` does not satisfy `hS`: the
  S-polynomial `y` cannot be represented with all nonzero product leading exponents
  strictly below `x`. Thus the hypothesis retains the essential strictness.
- Arbitrary characteristic, repeated generator occurrences in proof expressions,
  and arbitrary coefficient universe are allowed. No characteristic-zero instance,
  choice of finite generating list, or assumption `f ≠ 0` on an S-polynomial is added.

Searches for an existing criterion, using the prescribed wrapper with group Q120
and item `lem-sfb-buchberger-standard-representation-criterion`:

- `leanfinder`, query `Buchberger criterion from strict standard representations of S
  polynomials for arbitrary family of monic polynomials`: OK, 8 hits, including
  `MonomialOrder.sPolynomial_decomposition`, `sPolynomial_decomposition'`,
  `degree_sPolynomial`, `degree_sPolynomial_lt_sup_degree`, and `div`.
  These are cancellation identities, degree estimates, or division with remainder,
  not the criterion for every element of the generated ideal.
- `loogle`, query `MonomialOrder.sPolynomial`: OK, 12 hits. They include the
  existing definition, its expansion, zero cases, degree estimates, and decomposition;
  no matching criterion.
- `grep`, query `buchberger|[Gg]roebner|standardRepresentation`, subdirectory
  `RingTheory/MvPolynomial`: OK, 0 hits from the wrapper.
- `leansearch`, query `Buchberger criterion S polynomials strict standard
  representations arbitrary monic generating set`: OK, 8 hits. They include
  `sPolynomial_def`, `sPolynomial`, monomial multiplication identities,
  `sPolynomial_decomposition`, and `sPolynomial_mem_ideal`; no matching criterion.
- Direct `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf`, query
  `buchberger|[Gg]roebner|standardRepresentation|lem-sfb-buchberger-standard-representation-criterion`:
  no existing criterion. Project hits were the Groebner import and a discussion in
  `BoundedHilbertWeightPolynomials.lean`, and unrelated group representations.
  The direct node-id search in `WeilConjectures` returned no hit.
- Read all of `Mathlib.RingTheory.MvPolynomial.Groebner`: it gives the division
  algorithm and its set/single-generator variants, not this criterion. Direct source
  search for `buchberger_standard_representation|leading_monomial_dvd_of` in Mathlib
  and both project roots returned no hit, avoiding a name collision.

Validation: the required `scompile.py Q120 lem-sfb-buchberger-standard-representation-criterion`
compiled the single delivered module successfully in both sandbox and library views,
with no errors or non-sorry warnings. `set_option autoImplicit false` enforces explicit
variable binding. All Lean lines are at most 100 characters. The node JSON preserves
every inherited field and adds only `lean`; its signature is extracted verbatim
from the delivered source, and the record date is the current UTC date.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q120

This is a separate in-session rereading of the node and finished module; no second
agent was started, as required by the dispatcher brief. The maintainer supplies
the independent review.

The field and positive number of variables match the first sentence. `MonomialOrder`
provides the stated order without replacing it by a graded or lexicographic order.
`m.degree` and `m.Monic` reuse exactly the existing leading-exponent and leading-coefficient
notions. `hB` retains both nonzeroness and monicity. The expansion `sPolynomial_def`
has leading coefficients on the opposite generators; both are 1, so it agrees with
the displayed P, including its sign and the coordinatewise λ. `hS` quantifies over
all ordered pairs in `B`, and `q : B →₀ S` requires only finite support of the
coefficient family. Its equality multiplies coefficients by the generators, and its
strict inequality has precisely the nonzero-product guard from the node. `hf`, `hf0`,
and the conclusion quantify over every nonzero element of `Ideal.span B` and produce
one generator whose leading exponent is bounded in every coordinate. Empty and infinite
sets, constants, and zero S-polynomials are all retained. No mismatch was found and
no mathematical change was needed on this rereading.
