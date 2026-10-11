## Worker report

The module `Sheaf.Paper.NoetherianApproximation` states
`Algebra.exists_finiteType_subring_relativeGlobalCompleteIntersection`.
It binds a commutative ring `R`, natural numbers `n,c`, a family of `c`
multivariate polynomials in `n` variables, and the hypothesis that the
quotient by their ideal is a relative global complete intersection over `R`.
It concludes that there is a subring `R₀ : Subring R` which is finite type
as a `ℤ`-algebra, together with polynomials `f₀` over `R₀`, such that for
every relation index and monomial the coefficient of `f` is the image of the
corresponding coefficient of `f₀` in `R`; this is exactly containment of all
coefficients. The final conjunct states that the quotient by `f₀` is a
relative global complete intersection over `R₀`.

The hypothesis is rendered by
`IsRelativeGlobalCompleteIntersection (algebraMap R
(MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))`. The finite-type
clause is `Algebra.FiniteType ℤ R₀`; coefficient containment is the displayed
universal equality using `MvPolynomial.coeff` and the coercion `R₀ → R`; and
the conclusion is `IsRelativeGlobalCompleteIntersection` of the corresponding
`R₀` quotient.

The dependency declarations used are `MvPolynomial` from
`Mathlib.Algebra.MvPolynomial.Basic`, `Algebra.IsRelativeGlobalCompleteIntersection`
from `Sheaf.Paper.RelativeGlobalCompleteIntersection`, and
`Algebra.FiniteType` from `Mathlib.RingTheory.FiniteType`.

Edge cases checked: `n = 0` and `c = 0` are represented by `Fin 0`; the
coefficient condition is then vacuous as appropriate. The zero quotient is
allowed by the relative-complete-intersection definition, including the case
`c > n`.

Searches: `msearch.py leanfinder` for Noetherian approximation and finitely
generated subalgebras (only finite-presentation/finite-type results, no exact
match); `msearch.py loogle` for likely approximation declarations (no exact
match); `msearch.py grep` and `rg` over Mathlib and `WeilConjectures` for
complete-intersection/Noetherian-approximation declarations (no exact match).
The existing project definition `Sheaf.Paper.RelativeGlobalCompleteIntersection`
was read and reused; no duplicate notion was introduced.

## Earlier second reading (a previous round; superseded)

The signature was checked against the node clause by clause and compiles with
exactly the stated binders and conclusions; no statement change was needed.

## Second reading by F1

Read the item, all three statement-dependency nodes and their recorded declarations,
the original and revised Lean modules, and Stacks algebra.tex at Definition 00SP
and Lemma 00SU including its proof. The literature directory here is not populated;
the source was read in the local Stacks checkout `/home/ubuntu/c1-stacks-review`,
whose tags/tags verifies both labels. No source-wide Noetherian, domain, field,
characteristic, or nonzero-ring hypothesis is imposed by 00SU.

Clause-by-clause list and verdicts:

- Object R, arbitrary commutative ring: `(R : Type u) [CommRing R]`. Exact;
  no Noetherian, domain, or field instance.
- Objects n,c, nonnegative integers: `(n c : ℕ)`. Exact, no positivity condition.
- Objects f_1,...,f_c in the polynomial ring in n variables:
  `(f : Fin c → MvPolynomial (Fin n) R)`. Exact by the recorded `MvPolynomial`
  definition in Basic.lean:82 (finite sums of finitely supported monomials).
- Quotient by precisely these equations: `MvPolynomial (Fin n) R ⧸
  Ideal.span (Set.range f)` inside the new shared presentation predicate. Exact.
- Hypothesis that THIS presentation is a relative global complete intersection:
  `h : IsRelativeGlobalCompleteIntersectionPresentation f`. Exact after repair.
  The original `IsRelativeGlobalCompleteIntersection (algebraMap R ...)`
  existentially chose another presentation and did not constrain n,c,f.
- Conclusion subring R_0 inside R: `∃ (R₀ : Subring R)`. Exact, injective
  inclusion is the subtype coercion, and every subring contains the image of ℤ.
- Conclusion finite type over ℤ: `Algebra.FiniteType ℤ R₀`. Exact by
  FiniteType.lean:39, finitely generated top subalgebra. Not an additional
  Noetherian hypothesis; it is the specified conclusion.
- Conclusion all relation coefficients belong to R_0 and the same relations
  are regarded over R_0: `∃ f₀ : Fin c → MvPolynomial (Fin n) R₀` and
  `∀ i d, MvPolynomial.coeff d (f i) = (MvPolynomial.coeff d (f₀ i) : R)`.
  Exact. Coefficient equality for every monomial uniquely identifies the images
  with the original polynomials, so f₀ cannot select alternative equations.
- Conclusion that THIS descended presentation is a relative global complete
  intersection: `IsRelativeGlobalCompleteIntersectionPresentation f₀`. Exact
  after the same repair; the original conclusion only asserted existence of
  some complete-intersection presentation of the descended quotient.
- Quantifiers: arbitrary R,n,c,f with the stated hypothesis, then existence
  of R₀, its finite type property, and the unique coefficient lifts f₀ with
  the stated property. Exact. No universes or variables remain unbound.

Dependency reading: `def-weil-pbc-relative-global-complete-intersection` explicitly
contains both the fixed-presentation clause and the existential ring-map clause.
Its previous module implemented only the latter. Under brief §1(B) the delivery
adds `IsRelativeGlobalCompleteIntersectionPresentation` to that dependency's module,
using its recorded `Ideal.Fiber` and `topologicalKrullDim` encoding. It quantifies
all primes p of R, installs the supplied primality proof, and for each nonzero
fibre requires `c ≤ n` and dimension `n-c`. This is exactly signed dimension
n-c, with the inequality guarded by nonzero fibre. The original ring-map
predicate now refers to the shared fixed-presentation predicate: unfolding
restores precisely its old body, including its algebra isomorphism and arbitrary
R,S universes. No definition data is sorry and no theorem was proved. The item
and dependency node statements are unchanged; this is a Lean repair, not a
statement correction. No new definition node is needed because this dependency
already carries the missing clause.

Edge cases: `c = 0` gives the empty relation family; coefficient containment is
vacuous. `n = 0` has only the constant monomial (so its coefficient condition
is NOT generally vacuous, correcting the worker report's overbroad wording).
Both zero variables and zero relations are allowed. R = 0 and a zero quotient
have no nonzero fibres, so the fixed-presentation predicate is vacuous. For
c > n it forces every fibre to be zero rather than incorrectly accepting
truncated dimension zero. Empty spectra and the empty-cover case appear in
proof steps 4 and 6. All characteristics and arbitrary ring universe u are
covered; the subring, polynomials, and quotients stay in that universe. This
ring statement introduces no independent test-object or index universe.

Independent searches (2026-10-11):

- LeanFinder via msearch: "Descent of a polynomial quotient with all nonzero
  fibres of dimension number of variables minus number of relations to a
  finitely generated subring" returned SubmersivePresentation, finite
  presentation, Presentation.ModelOfHasCoeffs and smoothness declarations,
  no exact statement or fibre-dimension predicate.
- Loogle via msearch: `MvPolynomial, Subring, Algebra.FiniteType`: zero hits.
- LeanSearch via msearch: "relative global complete intersection fixed
  polynomial presentation fibre dimension n minus c": service unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.
- rg searched Mathlib RingTheory, upstream WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json for complete-intersection, relativeGlobal,
  NoetherianApproximation, and the proposed declaration names. Only the
  existential project predicate exists; no fixed-presentation declaration
  or exact approximation theorem. The equation-count-localization sibling
  already flags the distinction and states its presentation condition inline.
- Follow-up rg for `HasCoeffs`, `fg_subalgebra`, and Noetherian descent found
  Presentation/Core.lean and Smooth/NoetherianDescent.lean. These handle
  coefficient models and smooth algebras, not the nonzero-fibre dimension
  condition, and therefore do not replace this theorem or definition.

Mismatches repaired: fixed-presentation hypothesis and conclusion; missing
fixed-presentation dependency declaration; the incomplete proof docstring,
now all six steps with their cited nodes; malformed duplicated blueprint
markers; absent copyright header. Correct objects, binders, coefficient
condition, finite-type conclusion, and theorem name were retained. The
worker report is preserved as requested, with these corrections superseding
its original verdict and its earlier second reading.

Validation: both delivery modules compiled together using scompile.py, in
shared-definition then theorem order, exit 0, 1.5 seconds, no warnings. Both
node lean.statement fields are copied verbatim from their declaration signatures.
All Lean lines have at most 100 characters. The sole theorem proof is sorry.

## Dependency modules

`def-weil-pbc-relative-global-complete-intersection`:
`lean/Sheaf/Paper/RelativeGlobalCompleteIntersection.lean` now exposes the
fixed-presentation clause of Stacks 00SP needed by Lemma 00SU. The old record
only exposed the existential ring-map predicate and was unusable for the
specified equations. Its ring-map predicate is retained with the same
unfolded body and factored through the new shared presentation predicate.
Only this dependency's lean record changes; its statement, source,
mathlib_match and other fields are preserved. The record's note explains
this reason and its declarations list names both clauses.

## Reviewer fix (R-gna, stage 2)

The delivery edited lean/Sheaf/Paper/RelativeGlobalCompleteIntersection.lean to add its own `Algebra.IsRelativeGlobalCompleteIntersectionPresentation` (explicit `(_hp : p.IsPrime)` + `letI`) and re-recorded def-weil-pbc-relative-global-complete-intersection; that duplicates the landed J1 module Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation (cdb0af154, implicit {n c}, `[p.IsPrime]`), which is authoritative (H4). The dependency node and the module edit are reverted (`--revert-nodes`); NoetherianApproximation.lean now imports Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation. The theorem statement is unchanged and elaborates against the landed predicate.
