## Worker report

The module `Sheaf.Algebra.MvPolynomial.IntegralNewtonExpansion` states
`MvPolynomial.integral_newton_expansion`, with one `sorry`, and gives actual data for
four auxiliary declarations belonging to the formula introduced by this node:
`NewtonIndex`, `newtonBinomial`, `newtonExpansion`, and `newtonCoefficient`.
These are only the finite indexing and assembly of this node's displayed expressions;
they introduce no independent mathematical premise and need no new definition node.
The original DAG statement and every field other than `lean` are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Natural `r,D`: the explicit `(r D : ℕ)` binders. Rational polynomial in exactly
  `r` variables: `(P : MvPolynomial (Fin r) ℚ)`. Total degree at most `D`:
  `(hP : P.totalDegree ≤ D)`. Mathlib's `totalDegree` is the maximum of the sums
  of the exponents in the support, with value zero for the zero polynomial.
- A multi-index `b` of weight at most `D`: `NewtonIndex r D` is the subtype of
  functions `Fin r → Fin (D+1)` satisfying `∑ i, (b i).val ≤ D`. Every natural
  tuple of weight at most `D` has each coordinate at most `D`, so the finite box
  is a faithful representation of precisely those tuples, not a restriction.
- The product `B_b`: `newtonBinomial b = ∏ i, Ring.choose (X i) (b i)`.
  `Ring.choose` is Mathlib's existing binomial operation. Over the rational
  polynomial algebra, `Ring.descPochhammer_eq_factorial_smul_choose` identifies
  it with the falling product divided by the nonzero factorial. Its order-zero
  value is one. No second single-variable binomial operation is defined.
- The displayed finite expansion: `newtonExpansion r D c` is the sum of
  `c b • newtonBinomial (fun i ↦ (b.val i).val)` over the bounded indices.
  The theorem's first conjunct is `∃! c, P = newtonExpansion r D c`.
  Uniqueness is among ALL expansion coefficients, not only those satisfying
  the difference formula or the integrality conclusions.
- The difference coefficient formula: for EVERY `c` giving that expansion,
  the first inner conjunct states `c b = newtonCoefficient P ...` for every
  bounded index. This helper folds Mathlib's existing `fwdDiff` iterates,
  using displacement `Pi.single i (1 : ℚ)` on the rational coordinate space,
  over `List.finRange r`, starting from `fun x ↦ eval x P`, and evaluates at
  the zero tuple. By the definition of `fwdDiff`, this is evaluation of the
  successive polynomial substitutions `X_i ↦ X_i+1` minus the polynomial;
  thus it expresses exactly the node's polynomial forward differences at zero.
  Right-fold composition has the displayed operator order; the empty fold
  applies no difference.
- Integer values on `ℕ^r` imply integral coefficients: the second inner
  conjunct has hypothesis `∀ n : Fin r → ℕ, ∃ z : ℤ, eval ... P = (z : ℚ)`
  and conclusion `∀ b, ∃ z : ℤ, c b = (z : ℚ)`. This hypothesis is an
  implication, not a prerequisite for existence or uniqueness.
- Conversely integral coefficients imply integer values on `ℤ^r`: the third
  inner conjunct reverses the integrality implication and quantifies test
  points as `n : Fin r → ℤ`, including all negative coordinates.
- Every affine binomial, with arbitrary integer constant and slopes, has an
  integral bounded expansion: the final conjunct quantifies `(s : ℤ)`
  `(u : Fin r → ℤ)` `(t : ℕ)` and supplies `c : NewtonIndex r t → ℤ`.
  Its left side is `Ring.choose (C s + ∑ i, C (u i) * X i) t`; its right
  side is the bounded expansion with the integer coefficients cast to `ℚ`.
  There is no positivity restriction on `s` or `u`, and the bound is `t`.
- With zero variables the finite function space, its bounded subtype, and
  both evaluation grids are singletons; the empty product is one and the
  empty difference fold is the identity. The first and inner conjuncts then
  say exactly that the constant coefficient equals the rational constant,
  which is integer-valued if and only if that coefficient is an integer.
  This edge case is included by specialization, without extra assumptions.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`,
  `MvPolynomial.aeval`. Read the full signatures and docstrings. The statement
  uses the same `MvPolynomial` carrier and canonical `eval`, `C`, and `X`.
- Additional Mathlib APIs: `MvPolynomial.totalDegree` in
  `Mathlib.Algebra.MvPolynomial.Degrees`; `fwdDiff` in
  `Mathlib.Algebra.Group.ForwardDiff`; `Ring.choose` and its factorial
  characterization in `Mathlib.RingTheory.Binomial`. These are public imports.
- Proof dependency `lem-weil-pbc-triangular-change-of-basis`:
  `Sheaf.LinearAlgebra.TriangularChangeOfBasis`,
  `Module.Basis.exists_basis_of_triangular_unit_diagonal`, read in full and
  imported without `public` as the proof plan requires.
- Proof dependency `lem-sfb-integer-falling-factorial-divisibility`: its
  Mathlib match is `Ring.descPochhammer_eq_factorial_smul_choose`, not an
  absent Lean record. Read this signature and the cited
  `descPochhammer_eval_eq_prod_range`, `Polynomial.eval_eq_smeval`, and
  `Int.instBinomialRing`. The public Binomial import already provides these
  arithmetic proof inputs, so no dependency module is needed.

Source read: local `literature/stacks-project/algebra.tex`,
`definition-numerical-polynomial` and the following paragraph (Tag 00JX).
This is the univariate motivating result; the multivariate extension follows
exactly the accepted seven-step DAG proof. The theorem docstring includes all
seven steps and names the triangular and falling-factorial inputs.

Edge checks made before writing and during the second pass: `r = 0`, `D = 0`,
`P = 0`, and `t = 0` are all included. For `r=1`, `X² = 2 B₂ + B₁` checks the
normalization: the second difference at zero is `2`. For two variables,
`X₀X₁` has coefficient one at `(1,1)` and total degree two. The affine case
`s=0,u=-1,t=1` gives `-X`, checking that negative slopes are allowed; the
value `binom(-1,2)=1` checks the integer grid direction. The finite-box
encoding has exactly one zero index when `D=0` and when `r=0`.
No false statement, missing hypothesis, or node correction was found.

Searches actually run with `msearch.py Q66 lem-sfb-integral-newton-expansion`:

- LeanFinder, `Multivariate rational polynomials unique expansion product binomial basis forward differences integer coefficients`:
  eight hits, including `wittStructureRat_existsUnique`,
  `wittStructureInt_existsUnique`, `Polynomial.preHilbertPoly`, and
  `MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination`.
  None is this multivariate bounded Newton basis and integrality criterion.
- Loogle, `Polynomial.binomExpansion, fwdDiff, MvPolynomial.totalDegree`:
  zero hits for that combined query. Direct source inspection found the
  relevant separate APIs; the zero result is not claimed as their absence.
- Mathlib grep, `binomExpansion|binomialBasis|newton|Newton|choose.*[Bb]asis`:
  25 capped hits, chiefly unrelated chosen module bases and Hensel/Newton
  methods. Direct reading of `Polynomial.binomExpansion` showed it is a
  second-order Taylor formula, not this theorem.
- LeanSearch, `Integer valued multivariate rational polynomial Newton binomial expansion forward difference coefficients`:
  eight hits including `fwdDiff_iter_choose`, `shift_eq_sum_fwdDiff_iter`,
  `fwdDiff_iter_eq_sum_shift`, and `Polynomial.binomExpansion`. These provide
  univariate/function difference formulas, not the complete item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `newton|Newton|binomialBasis|IntValued|integer.valued` found the existing
  univariate Newton-series file and `CoordinateDifferences`, neither of
  which states this node. The latter integrates given coordinate differences;
  it does not assert the bounded binomial expansion or integral coefficients.
  Searching the node id in `lean/WeilConjectures` found no declaration.
- A source/name clash search for `newtonBinomial|newtonExpansion|newtonCoefficient|NewtonIndex|integral_newton_expansion`
  across Mathlib, `WeilConjectures`, and `Sheaf` found none before writing.

Validation: `scompile.py` compiled this file both under the sandbox probe module
and its actual library module name with no errors or warnings (13.0 s and
5.3 s respectively). All variables are explicitly bound; no extra universes
are needed for the node's finite variables and fixed rational coefficients.

## Second reading by Q66

This is a second pass by the original worker, not a claim of an independent
reader: the dispatcher's brief explicitly forbids starting other agents and
assigns the independent review to the maintainer. I reopened the DAG statement,
all seven proof steps, and the completed module and matched each clause as
above. In particular, existence and uniqueness are unconditional on integer
values, the difference formula applies to each bounded index, the first grid
is `ℕ^r` and the converse grid is all of `ℤ^r`, and affine coefficients are
arbitrary integers with bound `t`. The bounded subtype retains the empty tuple
at `r=0`, and the difference fold is the identity there. All four helper bodies
are real constructions using the existing Mathlib notions. No mismatch or
statement correction was needed.
