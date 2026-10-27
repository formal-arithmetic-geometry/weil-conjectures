## Worker report

Q29, stage 2, 2026-10-23. The delivery states
`Polynomial.eq_of_padic_root_product_abs_eq` in
`Sheaf.NumberTheory.Padics.RootProductRigidity`. Its only proof is `by sorry`.
There are no new definitions or dependency repairs. The existing item's only
changed field is `lean`; its accepted stage-1 split is preserved verbatim.

Source checked directly: `literature/milne-abelian-varieties_AV.pdf`, Chapter I,
Lemma 10.21 and proof, printed p.51 (PDF page 57). The node states precisely its
root-product rigidity criterion, including the degree-zero convention. The
module docstring contains all four steps of the accepted split: rational
denominators, coefficient approximation, minimal-polynomial root products,
and multiplicities detected at `x + ell^n`.

Hypothesis-by-hypothesis and clause-by-clause translation:

- A prime ell is `(ell : ℕ) [Fact ell.Prime]`. The base field K is literally
  `ℚ_[ell]`, Mathlib's Cauchy completion of Q for the normalized ell-adic norm.
- The chosen algebraic closure is `(Ω : Type u) [Field Ω]
  [Algebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. The universe `u` is explicit;
  the inclusion is `algebraMap ℚ_[ell] Ω`. No particular model is imposed.
- The extended absolute value is `(v : AbsoluteValue Ω ℝ)` together with
  `hv : ∀ x : ℚ_[ell], v (algebraMap ℚ_[ell] Ω x) = ‖x‖`. This fixes the
  normalization, and permits every extension as required. `AbsoluteValue`
  supplies multiplicativity, nonnegativity, positive definiteness and the
  triangle inequality. No extra normed-field topology is assumed on Ω.
- `(d : ℕ)` includes d = 0, and `(P Q : Polynomial ℚ_[ell])` are the two base
  polynomials. `hP : P.Monic` and `hQ : Q.Monic` give monicity;
  `hdegP : P.natDegree = d` and `hdegQ : Q.natDegree = d` give their same
  degree. Monicity excludes the zero polynomial, so natDegree is the actual
  degree, including nonzero constants.
- `(a b : Fin d → Ω)` are the root lists. The multiset equalities `ha` and
  `hb` identify `↑(List.ofFn a)` and `↑(List.ofFn b)` with the `roots` of the
  respective polynomials mapped along the field inclusion. `roots` includes
  multiplicities. Since Ω is an algebraic closure, these are complete lists;
  no order, distinctness or separability of P or Q is imposed.
- `h : ∀ F : Polynomial ℤ, ...` is exactly the test against every integral
  polynomial. `F.eval₂ (Int.castRingHom Ω) (a i)` evaluates the integral
  coefficients in the chosen closure; the analogous expression uses `b i`.
  The products `∏ i : Fin d, ...` are formed in Ω and then `v` is applied,
  exactly as in the node, rather than taking an unrelated resultant.
- The conclusion `P = Q` is equality in the original polynomial ring over
  `ℚ_[ell]`. The product over `Fin 0` is 1, implementing the stated empty
  product convention without an exceptional positive-degree assumption.

Dependency declarations read and used:

- `def-weil-l-adic-numbers` is a Mathlib leaf, with `Padic` and its norm in
  `Mathlib.NumberTheory.Padics.PadicNumbers`. Read `Padic` at line 531,
  `padicNormE` at line 601, the real norm and normed-field instance at lines
  797–806, and the normalization `Padic.norm_eq_zpow_neg_valuation` at 1053.
- `def-weil-polynomial-ring` records `Polynomial` from
  `Mathlib.Algebra.Polynomial.Basic`, read at line 74. Its `Monic`,
  `natDegree` and `leadingCoeff` were read in `Degree.Defs`, lines 48–61.
- `def-weil-algebraic-closure` is a Mathlib leaf. Its recorded interface
  explicitly names `IsAlgClosure` from `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  read at lines 264–268. This is the general chosen-closure notion in the
  statement, rather than restricting to the particular `AlgebraicClosure K`.
- `AbsoluteValue` was read in `Mathlib.Algebra.Order.AbsoluteValue.Basic`,
  lines 32–45; `Polynomial.roots` in `Mathlib.Algebra.Polynomial.Roots`,
  lines 56–60; and `Polynomial.eval₂` in `Eval.Defs`, lines 55–58.
- The stated proof dependencies `lem-sfb-ultrametric-criterion-natural-norms`
  and `lem-weil-alg-closed-linear-factorization` have Mathlib matches
  `isUltrametricDist_iff_forall_norm_natCast_le_one` in
  `Mathlib.Analysis.Normed.Field.Ultra` and `Polynomial.Splits.eq_prod_roots`
  in `Mathlib.Algebra.Polynomial.Splits`. Both were read and their modules
  are imported without `public` for the eventual proof.
- `lem-sfb-padic-minpoly-normed-separation` and
  `lem-sfb-padic-minpoly-root-product` are proof-only nodes with no Lean
  record or Mathlib match in the read tree. They introduce no object needed
  to type this statement. Their proof modules therefore cannot yet be
  imported; the maintainer adds imports when those nodes are stated, as
  required by stages/2-statements.md §3.7. They are retained in the proof
  docstring. No missing statement dependency or private notion is introduced.

Edge cases checked mathematically before finalizing:

- d = 0 forces the monic constants P = Q = 1, and both products are 1 even
  for F = 0. `Fin 0` and `List.ofFn` impose no spurious root or nonemptiness.
- d = 1 reduces to equality of integer-test absolute values on one root.
- Repeated roots, zero roots, and roots of absolute value greater than one
  are permitted by the multiset encoding; no distinct-root assumption is
  present. Different enumerations produce the same commutative product.
- For d > 0, F = 0 yields 0 = 0 and F = 1 yields 1 = 1. Neither test is
  mistaken for sufficient data: the hypothesis quantifies over every F.
- Unequal polynomials such as X and X - 1 are excluded by F = T, whose
  products have absolute values 0 and 1. Thus h is not a hollow condition.
- The prime 2 is included. No oddness, finite-dimensionality of Ω, root
  integrality, positive-degree bound or independent test universe is added.

Searches (actual results in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder` with "Two monic polynomials over the p adic
  numbers are equal if all integer test polynomials have equal absolute
  values of products over their roots": eight hits, including Witt-vector
  identities, PadicInt extensionality, Hensel's lemma and adjoin-root
  coefficient extensionality. None states this root-product norm criterion.
- `msearch.py ... loogle '"Padic", "Polynomial"'`: one hit,
  `padic_polynomial_dist`, an estimate for differences of evaluations, not
  rigidity of two monic polynomials.
- `msearch.py ... grep 'resultant.*(norm|abs)|norm.*resultant|root.*product'
  NumberTheory/Padics`: zero hits.
- `msearch.py ... leansearch` with "A monic p adic polynomial is determined
  by the absolute values of products of integer test polynomial evaluations
  at its roots": eight hits, including the product evaluation formulas for
  split monic polynomials, the rational padic absolute value, Monic and
  coefficient bounds. None is the requested implication.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `RootProductRigidity`,
  `padic_root_product`, `root_product_abs_eq`, `resultant.rigidity`, and
  `root.product.*(rigid|equal)`: no hits. Searching the node id in the
  upstream sources also found none.
- A broader padic/root/resultant search found upstream
  `WeilConjectures.NumberTheory.Padics.Extension`; its initial theorem and
  proof were read. Its Krasner approximation and finite-extension covering
  do not state the root-product rigidity result. A full Mathlib/project
  search for `10\.21`, the proposed name, or resultant theorem names found
  basic resultant identities, not this theorem.

No statement fault or disputed statement was found. The inherited BLOCKED
ending was for an already reviewed stage-1 split. The current queue records
this item in stage 2 with no Lean record, and brief-stage2 §0 explicitly
permits this handoff. No reviewed stage-1 field is changed.

## Second reading by Q29

This is a single dispatched worker, with an explicit instruction not to start
other agents; the maintainer performs the independent delivery review. This
section records a separate rereading of the current node, Milne p.51 and the
final sandbox module, not a claim that another worker reviewed it.

I checked each binder against the node again: prime ell and the literal
completion ℚ_[ell]; arbitrary algebraic closure with its inclusion; the
real absolute value agreeing with the normalized base norm; both monic
polynomials with equal nonnegative degree; two full root multisets including
multiplicity; every F in ℤ[T]; equality of absolute values of the products
computed in Ω; equality P = Q over the base. All clauses are present and no
extra restriction occurs. In particular `ha` and `hb` compare multisets, so
an ordering or simple-root condition is not hidden in the choice of lists.
The closure field is not required complete and no topology is imposed on it.
The degree-zero product is 1 on both sides. Source Lemma 10.21 has exactly the
same implication. No mathematical revision was needed. An explicit public
import of `Mathlib.Algebra.Polynomial.Basic` was added so the recorded
polynomial-ring dependency is visibly imported.

The module has `set_option autoImplicit false`, explicit universe u, one
named theorem, one expected sorry and no construction postponed as data.
The declaration's source and complete four-step proof plan are present.
There are no lines above 100 characters, private definitions, local notation,
or diagnostic commands. The JSON signature is extracted verbatim from the
keyword through the final result type, excluding `:=`, and only `lean` was
added to the copied node. The proof-only modules already stated in Mathlib
are imported. The two unstated proof-only nodes are explicitly accounted for
above rather than silently replaced or redeclared.

## Validation

The prescribed `scompile.py Q29 lem-sfb-padic-resultant-rigidity` compiled the
sandbox and library forms successfully (5.1 s and 3.2 s) with no errors or
unexpected warnings. Final compilation after the explicit import and the
prescribed `deliver2.py --no-push` preflight will be recorded below.

Final compilation after the explicit import passed both forms (1.6 s sandbox,
1.5 s library). `deliver2.py Q29 lem-sfb-padic-resultant-rigidity --no-push`
then reported `OK (dry run): commit a34a7e5c2a6 passes the preflight and
compiles; nothing pushed`. The copied node was also compared with the live
read tree: the sole changed field is `lean`.
