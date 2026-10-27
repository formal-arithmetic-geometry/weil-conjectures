## Worker report

The module `Sheaf.RingTheory.FilteredMonoidCoefficientLimit` states
`AddMonoidAlgebra.filteredMonoid_coefficient_limit`, with its sole proof `sorry`.
The node's statement, dependencies, proof and source are unchanged. No helper
notion or dependency repair is needed. The quantified `CommRing` and `Algebra`
on the literal function type follow the existing convention in
`Sheaf.RingTheory.MonoidCompletionCoefficients`; their operations are specified,
so pointwise multiplication is never substituted for convolution.

Hypotheses, in node order:

- A commutative ring: `(A : Type u) [CommRing A]`.
- The ideal and bijective completion map: `(I : Ideal A)
  [IsAdicComplete I A]`, equivalent to bijectivity by
  `AdicCompletion.of_bijective_iff` (read in Basic.lean).
- An arbitrary commutative additive monoid: `(P : Type v) [AddCommMonoid P]`,
  with an independent universe and no cancellation, finite generation, positivity,
  ordering, Noetherianity, localness or domain restriction.
- The length function: `ν : P → ℕ`, `hzero : ν 0 = 0`, and
  `hadd : ∀ p q, ν p + ν q ≤ ν (p + q)`.
- Finite sublevel sets at every positive n: `hfinite : ∀ n, 1 ≤ n →
  Set.Finite {p | ν p < n}`.
- Finite decomposition pairs at each p: `hpairs : ∀ p,
  Set.Finite {q : P × P | q.1 + q.2 = p}`.
- R is `AddMonoidAlgebra A P`, the existing finite monoid-sum construction used
  by `ToricMonoid.PolynomialRing` at zero variables. There is no redundant
  polynomial-variable carrier; this is precisely the node's declared A[P].
- The ideal is `J : Ideal (AddMonoidAlgebra A P)` and `hJ` is the stated
  equivalence for every polynomial F and every `n ≥ 1`. `F.coeff p` is its
  coefficient. Natural subtraction `n - ν p` is the nonnegative truncated
  subtraction in the node. Ideal powers are Mathlib's ideal products; exponent
  zero is the whole ring, not a closure of an ideal power.

Conclusions, in signature order:

- `ring`, `alg` and `c` assert the A-algebra structure on all functions `P → A`
  and the algebra equivalence from `AdicCompletion J (AddMonoidAlgebra A P)`.
- The first conjunct specifies pointwise addition for `ring.toAdd`.
- The second specifies multiplication for `ring.toMul` as
  `∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * b q.1.2`.
  Because of `hpairs` this finsum is exactly the finite convolution in the node.
- The third specifies the scalar map: a at zero and zero elsewhere. The unit
  and zero are consequently forced by the algebra and additive group laws;
  no unspecified ring operations remain.
- The fourth is the coefficient condition for every x,p,j,N,F: `1 ≤ j`,
  `j + ν p ≤ N`, and `Ideal.Quotient.mk (J ^ N) F =
  AdicCompletion.evalₐ J N x` imply equality of the two residues modulo `I ^ j`.
  It quantifies over every representative at every eligible level.
- The fifth is the inverse formula at every `n ≥ 1`: the projection of
  the explicitly instantiated `AlgEquiv.symm ... c a` is the quotient class of the sum of
  `AddMonoidAlgebra.single p (a p)` over `(hfinite n hn).toFinset`.
  `@AlgEquiv.symm` is supplied the quantified ring and algebra explicitly,
  avoiding synthesis of the pointwise Pi ring. It is the inverse of the same c.
- The sixth sends the canonical image under `AdicCompletion.of` of every
  `single p a` to the family `if q = p then a else 0`.
- The last quantifies over every other A-algebra equivalence d for the specified
  structures. The coefficient condition alone implies `d = c`, without assuming
  either the inverse formula or the monomial formula for d.

Dependency declarations and source reading:

- `def-weil-pbc-adically-complete-ring`: public import
  `Mathlib.RingTheory.AdicCompletion.Algebra` exposes its recorded Basic module;
  use `IsAdicComplete`. Read its complete class signature and
  `AdicCompletion.of_bijective_iff`.
- `def-weil-pbc-adic-completion`: the same import supplies `AdicCompletion`,
  `AdicCompletion.of`, its commutative ring and coefficient-algebra instances,
  and `AdicCompletion.evalₐ`. Read the compatible-sequence definition, the
  canonical map, and evalₐ's docstring and full definition. The index zero
  quotient is trivial, so Mathlib's nonnegative indexing is equivalent to the
  node's positive indexing, without an extra assumption.
- `def-trf-complete-toric-model`: public import
  `Sheaf.RingTheory.CompleteToricModel`; read the entire module, especially
  `ToricMonoid.PolynomialRing`, `Complete` and `IsCompleteModel`. Its underlying
  `AddMonoidAlgebra` is used directly for the node's zero-variable ring.
  All proof dependencies are already statement dependencies and publicly imported.
- Source checked directly: ILO PDF pp. 76--77 (printed pp. 70--71), Exposé VI
  1.6, via `pdftotext`, and the latest blueprint's local-term-locality statement.
  The node expressly attributes the coefficient refinement to an agent argument;
  the theorem docstring includes all seven steps, rather than attributing that
  refinement verbatim to ILO. Its proof uses completeness, compatibility,
  truncations, finite convolution, and coefficientwise separatedness exactly as
  the supplied node proof does.

Edge cases checked before writing:

- The zero ring is included; neither completion nor equivalence requires a
  nontriviality instance. If I is the unit ideal, completeness forces this case.
- I = 0 is allowed; completeness then identifies A with its constant residues.
- The one-element monoid is allowed, with ν(0) = 0 and J determined by I.
- Additional degree-zero exponents and finite noncancellative monoids are not
  excluded. Every degree-zero exponent is retained in every positive truncation.
- The threshold n = 1 and exponents with ν(p) = n give the correct I^0 condition;
  ν(p) < n, not ≤ n, defines the truncation set.
- j = 1 and N = j + ν(p) are included, with arbitrary larger levels and all
  representatives. The theorem requires no coefficient function to have finite
  support, and no empty generator-list case is excluded.
- No finite-generation or closed-powers theorem is used: the hypotheses are
  exactly the supplied finite-set conditions and the polynomial membership test.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Adic completion of filtered additive monoid algebra
  is all coefficient functions with finite convolution multiplication"`: eight
  hits, including `AdicCompletion`, its subalgebra, ring, algebra and Cauchy-sequence
  structures; none states reconstruction under this coefficient criterion.
- `msearch.py ... loogle "AdicCompletion, AddMonoidAlgebra"`: zero hits.
- `msearch.py ... grep "antidiagonal|convolution" Algebra/MonoidAlgebra`: ten
  displayed hits about finite-support algebras and their convolution formulas;
  none reconstructs unrestricted functions from completion residues.
- `msearch.py ... leansearch "Completion of monoid algebra coefficientwise ideal
  filtration all formal coefficient functions finite convolution"`: eight hits,
  including `AddMonoidAlgebra.mul_apply`, its antidiagonal formula, and ideal
  filtrations; none is this statement.
- `rg` over Mathlib's HahnSeries and MonoidAlgebra, project `WeilConjectures`
  and `Sheaf/RingTheory`: the nearest project results are
  `positiveMonoid_convolution_length` and `monoidCompletion_coefficients`.
  Both were opened and read. The latter additionally requires local Noetherian
  coefficients and an embedded positive finitely generated free-lattice monoid,
  so it cannot supply this general node. Its existential convolution-ring
  convention can and does apply here without a new notion.
- `grep -rn` for the item id in `lean/WeilConjectures` and `rg` for the proposed
  declaration/module name in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no existing declaration.

No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q48

A separate rereading by this worker compared the node and the final signature;
no additional agent was started, as the dispatch brief prohibits that. Independent
review is left to the maintainer's delivery review.

The rereading checked the explicit algebra structure against the pointwise Pi
instance, the arbitrary P and A universes, each of the two finite-set assumptions,
and the quantifiers in hJ. It checked all four bounds j ≥ 1, N ≥ j + ν(p),
n ≥ 1, and ν(p) < n individually. It also checked that uniqueness assumes only
the coefficient condition, that monomials allow all a,p,q (including a = 0 and
p = 0), and that the inverse truncation uses the same equivalence c. The compiler
found that `c.symm` tried to synthesize the pointwise ring; this was repaired by
passing the ring and algebra explicitly to `@AlgEquiv.symm`, the same inverse. No change
to the mathematical statement or DAG dependencies was needed.
