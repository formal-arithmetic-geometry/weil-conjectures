## Worker report

The module `Sheaf.RingTheory.BoundedMonomialStraightening` states
`Algebra.bounded_monomial_straightening` with `sorry`, and supplies two real
helper definitions for the node's own displayed notation:
`Algebra.orderedGeneratorMonomial` is the increasing-index list product of
powers, and `Algebra.boundedMonomialDegreeSpan` is exactly P_d, using
`Submodule.span`. Neither helper chooses data or postpones any proof. They
belong to this node and are listed in `lean.declarations`.
The natural-language statement and all dependencies are unchanged.

Hypotheses and notation, clause by clause:

- The field F is `(F : Type u) [Field F]`, with no characteristic restriction.
- The unital associative F-algebra A is `(A : Type v) [Ring A] [Algebra F A]`.
  A's multiplication need not commute. Mathlib's algebra structure gives the
  bilinear multiplication and its identity. The universes u and v are independent.
- The integer n >= 0 is represented by `n : ℕ`; q >= 2 is `q : ℕ` and `hq : 2 ≤ q`.
  This represents every allowed integer value, with no extra restriction.
- The ordered family y_1,...,y_n is `y : Fin n → A`; zero-based Lean indices
  merely relabel the given order.
- An unrestricted exponent vector is `Fin n → ℕ`.
  `orderedGeneratorMonomial y a` is `(List.ofFn fun i ↦ y i ^ a i).prod`,
  retaining the specified order. For bounded vectors, `Fin n → Fin q`
  encodes exactly 0 <= a_i < q. The total degree is `∑ i : Fin n, (a i : ℕ)`.
- `hbasis` asserts that there exists a `Module.Basis (Fin n → Fin q) F A`
  whose value at every index is the corresponding ordered monomial. Thus it
  assumes precisely that the indexed bounded monomials are a basis; it does
  not assume a preferred basis or any extra PBW theorem.
- W is written directly as `Submodule.span F (insert (1 : A) (Set.range y))`.
  `hcomm` quantifies over every i,j and puts `y j * y i - y i * y j` in W;
  `hpower` puts `y i ^ q` in W for every i.
- P_d is `boundedMonomialDegreeSpan F y q d`, where `d : ℤ`. Its generators
  are exactly the bounded monomials whose natural total degree, cast to ℤ,
  is at most d. There is no natural subtraction in a degree bound.

Conclusions, clause by clause:

- The first conjunct says `∀ d : ℤ, d < 0 → P_d = ⊥`, rendering the node's
  explicit observation P_d=0 for negative d.
- The second quantifies over `w : List (Fin n)` and asserts `(w.map y).prod ∈
  P_(w.length)`. Lists represent every ordered word of every generator length,
  including the empty word, so this is exactly the product-of-m-generators clause.
- The third quantifies over `r s : ℤ` with `0 ≤ r`, `0 ≤ s`. Its left hand
  side is the F-span of `{z | ∃ x ∈ P_r, ∃ t ∈ P_s, z = x * t}`; the inequality
  to P_(r+s) is the stated inclusion for the span of all products.
- The fourth quantifies over both bounded vectors a,b. Its first implication
  assumes `∀ i, (a i : ℕ) + (b i : ℕ) < q` and puts
  `y^a * y^b - y^(a+b)` in degree `(|a| : ℤ) + |b| - 1`.
  Its second implication assumes `∃ i, q ≤ (a i : ℕ) + (b i : ℕ)` and puts
  `y^a * y^b` in that same degree. The sum-vector product uses unrestricted
  natural exponents, so no modular or truncated addition is substituted.
- The final implication `n = 0 → ...` explicitly asserts
  `(⊤ : Submodule F A) = Submodule.span F {(1 : A)}` and `(1 : A) * 1 = 1`.
  This is A=F·1 and the indicated product identity.

Dependency declarations read and used:

- `def-weil-field` has Mathlib match `Field`, not a missing Lean record.
  Read its full declaration and docstring in `Mathlib.Algebra.Field.Defs`
  (line 180); that module is publicly imported.
- `def-weil-submodule-span` has Mathlib match `Submodule.span` in
  `Mathlib.LinearAlgebra.Span.Defs` (line 48). Read its full declaration and
  docstring, together with `mem_span`, `span_le`, `span_mono` and `subset_span`.
  That module is publicly imported and its span definition is used throughout.
  These are also the only proof dependencies, so there is no further proof-only
  import to add.
- For the basis assumption, use Mathlib's `Module.Basis` in
  `Mathlib.LinearAlgebra.Basis.Defs`. For the given algebra structure, use
  `Algebra` in `Mathlib.Algebra.Algebra.Defs`; its documentation identifies
  this with associative unital algebras and discusses bilinearity.

Source and proof check:

Read the PDF text of Milne, Algebraic Groups (2017), printed pp.200--204 and 207:
Theorem 10.36, the degree/inversion ordering and adjacent reductions, and
Theorem 10.40's reduction of a pth power to degree one. The node deliberately
abstracts these degree reductions and assumes the bounded basis; no general
PBW independence statement is introduced. The theorem docstring includes all
seven proof steps: span properties, adjacent inversions, contextual swap error,
q-power reduction, the two leading formulas, bilinear span multiplication, and
the empty family. In particular, the outer word-length induction proves the
error estimates before using multiplicativity, avoiding circular reasoning.

Edge cases checked before writing:

- n=0: the bounded index type has exactly one element, the empty function;
  its ordered product is 1. The basis hypothesis therefore implies A=F·1.
  Empty word products and the explicit final conclusion retain this case.
- a=b=0: m=0, so the error bound is genuinely degree -1, not degree zero;
  `1*1-1=0` belongs to the zero subspace. No overflow index can exist.
- q=2, n=1: both F[t]/(t²) and F[t]/(t²-t) fit, and the overflow product has
  degree at most one. No zero-power hypothesis stronger than membership in W
  was introduced.
- For any overflow, m>=q>=2, so the q-power reduction leaves context lengths
  m-q or m-q+1, both <=m-1. The scalar term allowed in W causes no problem.
- Negative d gives an empty generating set since all total degrees are
  nonnegative. r=0 or s=0 retains the span-of-products inclusion.
- Positive characteristic, q not prime, and noncommutative A are all allowed.
  No `CommRing A`, characteristic, finite-dimensionality, or nontriviality
  hypothesis was added. The basis already forces finite dimension and excludes
  a zero algebra. The general statement also allows the n=0 basis case.

Searches for existing declarations (all performed before the final module):

- `msearch.py leanfinder`: "In a noncommutative algebra with bounded ordered
  monomial basis and linear commutator and power relations, products have
  bounded total degree and truncated leading term". Eight hits were degree
  results for monoid algebras or commutative multivariate polynomials, including
  `AddMonoidAlgebra.apply_supDegree_add_supDegree` and
  `MonomialOrder.degree_mul_le`; none gives the stated bounded normal ordering.
- `msearch.py loogle`: `Module.Basis, Submodule.span`. Twelve basis/span results
  including `Module.Basis.span_eq`, `Module.Basis.mk` and `Module.Basis.span`;
  these supply the existing notions, but none states the degree reduction.
- `msearch.py grep`: `bounded.*monomial|ordered.*monomial|straighten|PBW`
  under Mathlib/RingTheory: zero hits.
- `msearch.py leansearch`: "Bounded ordered monomials in a noncommutative algebra
  with linear commutators and lower degree power relations give a multiplicative
  degree filtration". Eight hits, including `IsRingFiltration.toGradedMonoid`
  and commutative polynomial degree lemmas; no exact match. Read
  Mathlib/RingTheory/FilteredAlgebra/Basic.lean: multiplicativity is an assumption
  of `IsRingFiltration`, whereas our statement must derive it from the relations.
- `rg` for `bounded.*monomial|ordered.*monomial|PBW|[Ss]traightening` in the
  project's WeilConjectures and Sheaf sources, and `grep -rn` for the item id
  in WeilConjectures. No exact statement or reference to this item was found.
  The relevant nearby `Sheaf.RingTheory.BorelBialgebraMonomialBasis` was read:
  it constructs a basis of a connected graded bialgebra under different
  hypotheses, rather than proving this degree statement. Field p-basis results
  concern commutative field extensions and are also different.
- `rg` in `dag/lean_names_upstream.json`, Mathlib/Algebra/Lie and
  Mathlib/RingTheory/FilteredAlgebra found only the free-Lie file's comment that
  an alternative construction needs PBW, not the required theorem.
- Exact-name search for `orderedGeneratorMonomial`, `boundedMonomialDegreeSpan`
  and `bounded_monomial_straightening` across Mathlib and both project source
  roots found no declaration. The helpers are the node's own product and P_d
  notation, not independent missing notions requiring new DAG nodes.

No statement correction, disputed statement, or dependency-interface repair.
Server compilation through `scompile.py` succeeded for the sandbox and library
module in 1.3 seconds each, with no errors or non-sorry warnings. All universes
and variables are explicit (`set_option autoImplicit false`), every theorem has
only `sorry`, and every source line is at most 100 characters.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
