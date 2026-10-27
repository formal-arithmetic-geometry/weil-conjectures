## Worker report

The module `Sheaf.RingTheory.ReducedIntegralPolynomialGeneralizedInverse` states
`IsIntegral.exists_polynomial_generalized_inverse`, with `sorry` as its only proof.
No new definitions, dependency repairs, or statement corrections are needed.
The current item is queued for stage 2 and has no Lean record; the inherited
unchanged-item failure concerned its accepted stage-1 split. This delivery preserves
that split and adds the missing Lean statement.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The commutative k-algebra B is `{B : Type v} [CommRing B] [Algebra k B]`.
  The structural map is the algebra map used by `Polynomial.aeval`.
- Reducedness is `[IsReduced B]`. Its defining field says every nilpotent is zero;
  for a commutative ring this is exactly the node's condition on positive powers.
  Including exponent zero in Mathlib's nilpotent definition adds no restriction:
  if the zeroth power is zero, then 1 = 0 and B is already the zero ring.
- The element is `{x : B}` and its integrality is `(hx : IsIntegral k x)`.
- The polynomial witness is `∃ q : Polynomial k`.
- Writing y = q(x) using k → B is rendered by `Polynomial.aeval x q`.
  The single equation is exactly `x ^ 2 * Polynomial.aeval x q = x`.
- The statement imposes no nontriviality condition on B and no nonzero condition on x.
  The universes u and v are explicit and independent; `autoImplicit` is disabled.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, definition and docstring
  at line 180. This is the node's Mathlib match, requiring no new Lean record.
- `def-weil-pbc-integral-closure`: the recorded module
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` is imported. Its `integralClosure`
  at line 216 has carrier `{r | IsIntegral R r}`. The statement uses the recorded
  `IsIntegral`, whose complete definition and docstring were read in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, lines 34–54; it uses a monic
  polynomial and evaluation through `algebraMap`. The dependency's additional
  `IsIntegrallyClosedIn` was read at IntegrallyClosed.lean:66, but is not needed here.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`,
  lines 66–75, is the recorded finitely supported coefficient construction.
- The inline reducedness uses Mathlib's `IsReduced`,
  `Mathlib.Algebra.GroupWithZero.Basic`, lines 189–193.
  Evaluation uses `Polynomial.aeval`, `Mathlib.Algebra.Polynomial.AlgebraMap`,
  lines 239–258, the algebra homomorphism evaluating X at x.

The theorem docstring carries all three coefficient-argument steps of the node,
including the polynomial choice and the handling of the zero ring. The source
was read at `literature/stacks-project/varieties.tex`, Tag 04MI,
`lemma-integral-closure-ground-field`, and `algebra.tex`, Tags 00J6 and 00JA,
`lemma-finite-dimensional-algebra` and `lemma-product-local`. The current blueprint
unit proof was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, part (3).
The polynomial strengthening is the node's explicit agent-written algebra input,
not a claim that Stacks 04MI states this exact refinement.

Edge cases checked before writing:

- For x = 0, q = 0 satisfies the equation.
- In the zero algebra, q = 0 satisfies the equation; Mathlib supplies IsReduced
  for a subsingleton. No `[Nontrivial B]` is present.
- In a product k × k, x = (0,1) has q = 1 as witness. This checks that x need
  not be a unit or a non-zero-divisor, and excludes the tempting domain-only API.
- For a scalar x = c with c nonzero, the constant q = c inverse works.
- In positive characteristic and for inseparable integral elements the coefficient
  argument uses only the inverse of the first nonzero coefficient, not separability.
- When the annihilator is a pure power of X, the tail polynomial h is zero;
  reducedness gives x = 0, consistent with the conclusion.

Searches actually run with `msearch.py NY` on this item:

- LeanFinder: "An integral element of a reduced commutative algebra over a field
  has a polynomial q with x squared times q(x) equal to x": eight results, including
  `minpoly.isRadical`, `IsIntegral`, and the integral-closure power lemmas.
  None states the required polynomial generalized inverse.
- Loogle: `IsIntegral, IsReduced`: one result,
  `IsAlgebraic.iff_exists_smul_integral`, concerning algebraicity rather than this equation.
- Mathlib grep in RingTheory:
  `generalizedInverse|generalisedInverse|exists_eq_mul_self_mul|IsVonNeumannRegular`:
  zero hits.
- LeanSearch: "An integral element in a reduced algebra over a field admits a
  polynomial generalized inverse x squared y equals x": eight results concerning
  integrality, ordinary inverse membership, and algebraicity. The inverse lemmas
  require division rings and do not allow the node's reduced zero divisors.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for generalized inverses,
  reduced/integral combinations, and `exists_eq_mul_self_mul` found only general
  absolutely-flat-ring consequences and tensor-product results, not this theorem.
  `Ring.AbsolutelyFlat.exists_eq_mul_self_mul` does not provide a polynomial witness
  from the present elementwise-integrality hypothesis. Direct grep for this node's
  id in `lean/WeilConjectures` found no declaration. The proposed declaration name
  was also searched in Mathlib and both project source trees, with no hit.

No statement dispute or node fault was found. The prescribed `scompile.py` completed
with exit code 0 in both sandbox and library-module modes (4.1 s and 1.0 s),
with no errors or unexpected warnings. The node copy differs only in `lean`;
all source lines are at most 100 characters. The prescribed delivery dry run
provides the final preflight and repeated per-file compilation.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
