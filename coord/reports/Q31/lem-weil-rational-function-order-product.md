## Worker report

The module `Sheaf.FieldTheory.RationalFunctionOrderProduct` states all three clauses of
`lem-weil-rational-function-order-product`. Its three named theorems have `sorry` proofs;
there are no new definitions, new nodes, dependency repairs, or statement changes.
Each theorem's docstring gives its source and the corresponding steps of the node's proof.
The source proof was read in
`literature/blueprint/master/blueprint/sec-zeta-weil/sk-thm-weil4/thm-weil-final-betti.md`,
paragraphs 2–4, where the endpoint-pole calculation uses this bookkeeping.

Hypotheses and conclusions match as follows:

- The arbitrary field is `{K : Type u} [Field K]`, with an explicitly declared universe `u`.
  The point is `(c : K)`, polynomials are `K[X]`, and rational functions are `RatFunc K`.
- Clause 1 is `Polynomial.rootMultiplicity_orderProduct_facts`. Its `(P Q : K[X])`,
  `(hP : P ≠ 0)` and `(hQ : Q ≠ 0)` are the two nonzero polynomials in the node.
  The first conjunct is `rootMultiplicity c P = 0 ↔ P.eval c ≠ 0`.
  The second is multiplicity additivity for `P * Q`.
  The third quantifies `v : Kˣ` and states multiplicity one for
  `C (v : K) * (X - C c)`. The fourth states multiplicity one for
  `1 - C c⁻¹ * X` under exactly `c ≠ 0`.
- Clause 2 is `RatFunc.rootMultiplicity_prod_zpow`. The inclusive list `P₀,…,Pₙ` is
  `(n : ℕ) (P : Fin (n + 1) → K[X])`; integer exponents are
  `(e : Fin (n + 1) → ℤ)`. The hypothesis `hP` asserts nonzeroness for every factor.
  `(R : RatFunc K)` together with `hR : R = ∏ j, (algebraMap _ _ (P j)) ^ e j`
  binds precisely the product called `R` in the statement; the product identity is its
  defining equation, not a restriction on the allowed polynomials or exponents.
  Its first conclusion is `R ≠ 0`, so nonzeroness of the product is established as stated,
  rather than assumed. The reduced `N` and `D` are `R.num` and `R.denom`;
  Mathlib's `num_div_denom`, `monic_denom`, and `isCoprime_num_denom` give exactly
  the specified presentation. The next conjunct casts both natural multiplicities to
  integers before subtracting and equates their difference to the explicit integer sum
  `∑ j, e j * (rootMultiplicity c (P j) : ℤ)` (the node's `ν`). No natural-number
  subtraction truncates negative orders. The disjunction
  `rootMultiplicity c R.num = 0 ∨ rootMultiplicity c R.denom = 0` says at most one
  multiplicity is nonzero. For each integer `m` with `1 ≤ m`, the next conjunct is
  denominator multiplicity `m` iff the signed sum is `-m`. This is exactly pole order
  as recorded by `def-weil-rational-function-pole-order`'s Mathlib match.
  The last conjunct is `R.denom.eval c ≠ 0` iff the signed sum is nonnegative,
  exactly the regularity definition in `def-weil-rational-function-field`.
- Clause 3 is `RatFunc.rootMultiplicity_denom_prod_zpow_eq_one`. It retains the
  field, point, nonzero polynomial family, exponents and defining equation for `R`.
  `j₀ : Fin (n + 1)`, `he : e j₀ = -1`, and
  `hm : rootMultiplicity c (P j₀) = 1` render the distinguished index and its two
  properties. `hother` states `(P j).eval c ≠ 0` for every `j ≠ j₀`.
  The conclusion `rootMultiplicity c R.denom = 1` is exactly a simple pole.
  Clause 2 already supplies nonzeroness of this same product.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-polynomial-ring`: `Polynomial`, in `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-rational-function-field`: `RatFunc`, in `Mathlib.FieldTheory.RatFunc.Defs`;
  `RatFunc.num`, `RatFunc.denom`, `RatFunc.monic_denom`,
  `RatFunc.isCoprime_num_denom`, `RatFunc.num_div_denom`, in
  `Mathlib.FieldTheory.RatFunc.Basic`. These provide the actual reduced presentation.
- `def-weil-root-multiplicity` and `def-weil-rational-function-pole-order`:
  `Polynomial.rootMultiplicity`, in `Mathlib.Algebra.Polynomial.Div`.
  The pole node explicitly records specialization to `R.denom` as its interface;
  no replacement definition is necessary.
- `def-weil-coprime-polynomials`: `IsCoprime`, in `Mathlib.RingTheory.Coprime.Basic`;
  coprimality of the canonical presentation is supplied by Mathlib as above.
- `def-weil-polynomial-root`: `Polynomial.eval₂`, and its identity-map specialization
  `Polynomial.eval`, in `Mathlib.Algebra.Polynomial.Eval.Defs`.
- Proof leaves `lem-weil-root-multiplicity-pos-iff` and
  `lem-weil-root-multiplicity-mul`: `Polynomial.rootMultiplicity_pos` in
  `Mathlib.Algebra.Polynomial.Div`, and `Polynomial.rootMultiplicity_mul` in
  `Mathlib.Algebra.Polynomial.RingDivision`. The latter is publicly imported;
  the former is available through its imports. All remaining statement/proof dependency
  modules are also transitive imports of the two public imports.

Edge cases checked before drafting: `n = 0` gives one factor, as the inclusive list
requires. There is no requirement `n > 0`. An empty positive- or negative-exponent
subproduct is one. All exponents zero give `R = 1`, signed order zero, no positive pole,
and regularity everywhere. Constant nonzero polynomials have multiplicity zero.
Equal numerator and denominator factors cancel, so the signed order can be zero despite
positive unreduced multiplicities. Positive and negative signed orders give a zero or
pole respectively; the integer casts preserve this distinction. At `c = 0` all general
clauses apply; only the explicitly reciprocal linear-factor identity is conditional on
`c ≠ 0`. Units include every nonzero scalar in every characteristic, including
characteristic two. Zero polynomial factors are excluded exactly as in the node.
The pole criterion quantifies integers `m ≥ 1`, including arbitrarily large orders.
No false or untypable clause was found; no STATEMENT-DISPUTED flag is needed.

Searches before writing:

1. `msearch.py ... leanfinder "root multiplicity of numerator minus denominator of a
   product of integer powers of nonzero polynomials rational functions pole order"`:
   eight hits. They concern meromorphic orders over normed fields, integer degree of
   rational functions, valuation at `(X)`, and `rootMultiplicity_mul'`. None gives
   this statement for arbitrary fields and arbitrary points with reduced denominators.
2. `msearch.py ... loogle "RatFunc.num, RatFunc.denom, Polynomial.rootMultiplicity"`:
   zero hits.
3. `msearch.py ... grep "rootMultiplicity" FieldTheory/RatFunc`: zero hits.
4. `rg -n "rootMultiplicity|rational.function.order.product"` in upstream
   `WeilConjectures` and project `lean/Sheaf`: only unrelated multiplicity uses in
   integral closures, pro-etale integral-local rings, and separability. No match.
   `grep -rn "lem-weil-rational-function-order-product"` in upstream: no match.
5. Name search for the three proposed declaration names in `dag/lean_names_upstream.json`,
   Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`: no collisions.
6. Direct Mathlib signature/docstring reads verified all dependency declarations above,
   including the numerator/denominator normalization and the identity-map evaluation.

Validation: `scompile.py Q31 lem-weil-rational-function-order-product` compiled the
module successfully as both sandbox and library module, with no errors or warnings.
Maximum Lean source line width is 96. All binders and the universe are explicit.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
