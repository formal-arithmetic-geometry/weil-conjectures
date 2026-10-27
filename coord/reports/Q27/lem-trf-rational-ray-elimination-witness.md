## Worker report

The module `Sheaf.TraceFormula.RationalRayEliminationWitness` states
`Weil.rationalRayEliminationWitness`. Its sole theorem has proof `by sorry`;
there are no new definitions, dependency repairs, or statement corrections.
The existing node is changed only in `lean`.

Clause-by-clause correspondence:

- The finite index set is `{I : Type u} [Finite I]`, with `u` explicitly declared.
  Passing from a finite set to its subtype gives exactly this indexing; no enumeration,
  decidable equality, cardinality bound, or nonemptiness is required.
- The rational coefficients are `(a b : I → ℚ)`.
- The three sign classes are rendered directly by `a h = 0`, `0 < a i`,
  and `a j < 0`. They are not independently supplied sets.
- Nonnegative constants on the zero class are precisely
  `hzero : ∀ h : I, a h = 0 → 0 ≤ b h`.
- Nonnegative constants on the positive class are precisely
  `hpos : ∀ i : I, 0 < a i → 0 ≤ b i`.
- Pairwise compatibility is precisely
  `hmixed : ∀ i j : I, 0 < a i → a j < 0 → 0 ≤ a i * b j - a j * b i`.
- The set B is written without a helper definition as
  `insert 0 ((fun j : I ↦ b j / a j) '' {j : I | a j < 0})`.
  Set insertion is exactly union with the singleton zero; the image ranges exactly
  over negative indices, so no ratio with zero denominator contributes to B.
- Finiteness and nonemptiness are the first two conjuncts, `.Finite` and `.Nonempty`,
  of that exact set.
- The rational greatest member is `∃ T : ℚ, IsGreatest (...) T ∧ ...`.
  Mathlib's `IsGreatest` includes membership as well as the upper-bound property;
  this does not replace a greatest member by a mere upper bound or a supremum.
- Its nonnegativity is `0 ≤ T`.
- Every negative-index lower bound is `(∀ j : I, a j < 0 → b j / a j ≤ T)`.
- Every positive-index upper bound is `(∀ i : I, 0 < a i → T ≤ b i / a i)`.
- All residual inequalities are `(∀ i : I, 0 ≤ b i - T * a i)`.
- The empty negative-class normalization is
  `({j : I | a j < 0} = ∅ → T = 0)`.
  No global assumption asserts that any sign class or the index type is inhabited.

Dependency declarations used: the only `stmt_deps` node, `def-weil-field`, has
`mathlib_match: ["Field"]` and no Lean record. Its full definition and docstring
were read in `Mathlib.Algebra.Field.Defs`: `class Field (K : Type u) extends
CommRing K, DivisionRing K`. The specialized instance `Rat.instField : Field ℚ`
in `Mathlib.Algebra.Field.Rat` supplies exactly that structure; it is publicly
imported by `Mathlib.Algebra.Order.Field.Rat`. Other standard notions come from
`Mathlib.Data.Set.Finite.Basic` (`Set.Finite`) and `Mathlib.Order.Bounds.Defs`
(`IsGreatest` and `upperBounds`). There are no proof dependencies to import.
No general ordered-field replacement is made: the coefficients and witness remain ℚ.

Source reading: read the item's full four-step agent-written proof and its source
qualification. Read the current blueprint's `sk-i-curve-zero/_section.md` and
`lem-trf-local-term-locality.md` and `.proof.md`. As the node explicitly records,
that blueprint ancestry is historical; it does not itself state the cone argument.
The declaration docstring attributes the elementary proof to the extracted auxiliary
assertion and treats ILO VIII Remark 3.1.29 as contextual only. It carries all four
proof steps, including the positive denominator calculation and empty-class cases.

Edge cases checked before writing: empty I gives B = {0} and T = 0; no negative
indices gives the same singleton, including positive/zero-only systems; no positive
indices makes all positive upper bounds and mixed hypotheses vacuous; all slopes
zero leaves exactly the hypotheses on constants. Negative slopes with either sign
of the constant are allowed. For example a = -1, b = -1 gives T = 1, whereas
positive lower-bound ratios can be absent and T can remain zero. Duplicate ratios
are harmless because B is a set. In every division used by a sign-restricted bound,
the denominator is nonzero. After writing, an independent exact-Fraction calculation
exhausted 362 admissible coefficient systems of lengths 0--3 with coefficients in
{-1,0,1}; membership, all bounds, residuals, and empty-class normalization passed.
This is a finite sanity check, not a proof of the theorem.

Searches made with the required `msearch.py Q27 <item>` wrapper:

- LeanFinder: "For finitely many rational inequalities with nonnegative constant
  terms for nonnegative slopes and compatible upper and lower bounds, the maximum
  of zero and all lower bound ratios solves every inequality". Eight results,
  including `Mathlib.Tactic.Bound.boundLinarith`, `Archimedean.ratLt'_bddAbove`,
  and recurrence/regularity bounds; no complete matching assertion.
- LeanSearch: "For a finite rational system of signed linear inequalities, the
  maximum of zero and the lower bounds is a feasible solution when each lower
  bound is below each upper bound". Returned `lowerBounds_le_upperBounds`,
  `Rat.le_coe_toNNRat`, `Finset.max'_le`, `Finset.le_max'`, `Finset.max'_le_iff`,
  and tactic internals; none states the signed compatibility-to-feasibility result.
- Loogle: `Finset.isGreatest_max'`. One exact API hit in `Mathlib.Data.Finset.Max`;
  read its signature and the max'/membership/bounds source at lines 180--228.
  It covers only the finite maximum, not this theorem's signed inequalities.
  An initial malformed query `Finset.max\x27, IsGreatest` returned an unknown
  identifier `x27`; the valid query above replaced it.
- Wrapper grep: `rational.*inequal|Fourier.Motzkin|isGreatest_max`.
  Fifteen hits, finite-maximum API and Fourier-Motzkin tactic implementation/docs;
  no full matching theorem.
- Direct searches in both `lean/WeilConjectures` and `lean/Sheaf`:
  `rational_ray|rationalRay|ray_elimination|rayElimination|rational-ray-elimination-witness|Fourier.Motzkin`
  gave no match; `ray.*(elimination|Elimination)|[Rr]ational.*[Ww]itness|signed.*inequal`
  gave only unrelated witness/coherence comments. The required recursive literal
  node-id search in `lean/WeilConjectures` had no matches. A declaration-name search
  for `rationalRayEliminationWitness` in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` had no matches.

Validation: required server `scompile.py` compiled the sandbox module and the
library-named module separately, each in 0.7 seconds, with no errors or warnings.
All Lean lines are at most 100 characters; every variable and universe is bound
explicitly. No statement dispute or node fault was found.

## Second reading by Q27

A separate second pass by the same worker compared the full node with the final
module; no other worker was started, as the dispatcher brief prohibits that.
The maintainer's independent review remains the independent human/process check.
This pass verified: `[Finite I]` does not entail `Nonempty I`; zero-slope constants
are separately assumed; positive constants are not inadvertently required on
negative slopes; `hmixed` orders the positive index first, with exactly the stated
subtraction; B uses b/a rather than a/b; `IsGreatest` asserts membership; both
sign-restricted bounds use the stated directions; every residual has T*a, and
empty negative indices imply T=0 within the same witness conjunction. The finite
and nonempty clauses are both present. There is no let/have abbreviation, hidden
hypothesis, extra structure, or characteristic generalization. No mismatch was
found and no correction was required in this pass.
