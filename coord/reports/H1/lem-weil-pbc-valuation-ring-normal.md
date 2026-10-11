## Worker report

The module `Sheaf.RingTheory.ValuationRingNormal` states
`isDomain_isIntegrallyClosed_of_fractionField_element_or_inverse`, with proof `sorry`.
It introduces no definition and proves nothing. The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`.
- A is a domain: `[IsDomain A]`. This includes nontriviality.
- K is its fraction field: `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`. The algebra map is the canonical embedding; fraction-ring
  injectivity ensures that membership means membership in A itself.
- For each nonzero x in K, x or its inverse belongs to A: the single explicit hypothesis
  `h : ∀ x : K, x ≠ 0 → (∃ a : A, algebraMap A K a = x) ∨
  (∃ a : A, algebraMap A K a = x⁻¹)`. Nonzero elements of a field are precisely its
  multiplicative units, so this renders the node's quantification over K^×.
- A is a normal domain: `IsDomain A ∧ IsIntegrallyClosed A`, the exact domain
  specialization recorded by `def-weil-pbc-normal-ring`.
- The explanatory clause that every integral element of K belongs to A is the
  elementwise meaning of `IsIntegrallyClosed A`: Mathlib's `isIntegrallyClosed_iff`
  for this K gives `∀ {x : K}, IsIntegral A x → ∃ a, algebraMap A K a = x`.
  It is not an additional conclusion, and is not duplicated as a redundant conjunct.

Dependency declarations read and used: `def-weil-pbc-normal-ring` is a Mathlib leaf,
with no `lean` record. Its `mathlib_match` records `IsDomain`, `IsIntegrallyClosed`,
and `Localization.AtPrime`. Read `IsDomain` and its docstring in
`Mathlib.Algebra.Ring.Defs` and `IsIntegrallyClosedIn`, `IsIntegrallyClosed`, and
`isIntegrallyClosed_iff` in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
The domain clause uses the first two; the localization clause of normal *rings* is
not invoked for this node, which states normal *domain*. The only import is
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, which supplies the conclusion
and the fraction-field API. `IsFractionRing` was also read in
`Mathlib.RingTheory.Localization.FractionRing` (localization at non-zero-divisors).

Edge cases: x = 0 is intentionally outside the valuation hypothesis, and is always
in the image of A. Fields A are included (the first disjunct always holds with
K = A). The zero ring is excluded exactly by the source's domain hypothesis.
No rank, dimension, local-Noetherian, characteristic, or proper-subring assumption
is imposed. Universes u and v are explicitly bound and independent: no quantification
is restricted to a universe smaller than the domain. The integral equation has
positive degree since a degree-zero monic polynomial is 1 in the nontrivial field;
the proof in the docstring handles degree one explicitly.

Source checked: the local Stacks checkout is absent on this machine, so opened
https://stacks.math.columbia.edu/tag/00IC (Lemma 10.50.3): a valuation ring is a normal
domain. Its printed proof uses domination; the DAG explicitly records the direct
monic-equation argument for its equivalent element-or-inverse characterization.
The module docstring preserves all three of those proof steps.

Searches (2026-10-11):

- `msearch.py ... leanfinder "A valuation domain is integrally closed in its fraction field"`:
  eight hits, including `Valuation.Integers.isIntegrallyClosed` and the instances
  `instIsIntegrallyClosedSubtypeMemSubring` and
  `instIsIntegrallyClosedSubtypeMemValuationSubring` in
  `Mathlib.RingTheory.Valuation.LocalSubring`.
- `msearch.py ... loogle "IsValuationRing, IsIntegrallyClosed"`: no hits; the service
  reports unknown identifier `IsValuationRing`.
- `msearch.py ... grep "isIntegrallyClosed|class IsValuationRing" RingTheory/Valuation`:
  ten hits in Integral.lean and LocalSubring.lean. Read the candidate declarations:
  `Valuation.Integers.isIntegrallyClosed` takes a valuation and its `Integers` witness;
  the LocalSubring instances take a bundled `ValuationSubring K`. Neither has the
  node's arbitrary domain A, fraction-field K, and explicit element-or-inverse
  hypothesis. They provide tools for a future proof, not an exact recorded signature.
  No `IsValuationRing` class occurs in the installed valuation sources; the old
  stage-1 search results mentioning that name do not identify an available declaration.
- `msearch.py ... leansearch "a domain in which every nonzero fraction or its inverse belongs
  to the ring is integrally closed"`: unavailable, Internal Server Error.
- `rg` in Mathlib, WeilConjectures, and lean/Sheaf for
  `isDomain_isIntegrallyClosed_of_fractionField_element_or_inverse|element_or_inverse|
  exists.*inv.*integrally|integrally.*exists.*inv`: no hits.
- `rg` in WeilConjectures and lean/Sheaf for `isIntegrallyClosed` and the valuation
  criterion: related geometric normality results and existing normal-ring statements,
  but no exact criterion theorem. Searching WeilConjectures for the node id returns
  no hit; searching `dag/lean_names_upstream.json` for it also returns no hit.

No new nodes or dependency modules are needed: the valuation criterion is supplied
in full as a hypothesis, and the normal-domain notion is already recorded by the
sole dependency. No statement dispute or correction was found.

Validation: the module compiled on the server via `scompile.py` in 1.4 seconds,
exit code 0, with no warnings or errors. Dry-run delivery is checked as the final
worker step; the independent second reader supplies their reading and pushes.

## Second reading by H1

Read the item node, its three proof steps, the complete delivered module, and the
sole dependency `def-weil-pbc-normal-ring` independently. The dependency now has
an existing Lean record (the worker report's description of it as having no record
is stale): it explicitly prescribes `IsDomain A ∧ IsIntegrallyClosed A` for a normal
domain. This supports the delivered conclusion without a dependency module.

Source reading: the local Stacks checkout is absent. Read the actual `algebra.tex`
from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
at `definition-valuation-ring`, `lemma-valuation-ring-normal`,
`lemma-valuation-ring-x-or-x-inverse`, and `lemma-x-or-x-inverse-valuation-ring`;
also checked https://stacks.math.columbia.edu/tag/00IC and the surrounding section
https://stacks.math.columbia.edu/tag/00I8. The source defines valuation rings as
local domains maximal under domination. The next two lemmas establish equivalence
with the element-or-inverse criterion, including fields. Thus the node's explicit
criterion has precisely the source's scope; locality is a consequence, not a
missing hypothesis. No global Noetherianity, rank or characteristic assumption occurs.

Object, hypothesis and conclusion checklist:

- Commutative ring A: `(A : Type u) [CommRing A]`. Exact; arbitrary commutative rings
  with identity, before imposing the following domain condition.
- A is a domain: `[IsDomain A]`. Exact. Read Mathlib.Algebra.Ring.Defs, where this
  is nontriviality plus cancellability away from zero; with CommRing it is an
  integral domain.
- Fraction field K of this A: `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`. Exact. Read Mathlib.RingTheory.Localization.FractionRing:
  IsFractionRing is localization at non-zero-divisors, and its algebra map is
  injective. The algebra structure names the embedding, rather than adding an
  unrelated action. The field is arbitrary, not an algebraic closure or extension
  bigger than the fraction field.
- For every x in K^times, x or its inverse belongs to A: the binder `h` quantifies
  `∀ x : K, x ≠ 0 →` followed by the two existential algebra-map equations.
  Exact: in a field nonzero elements are exactly units; image membership is exactly
  membership in A under its canonical embedding. The disjunction permits both.
- Conclusion A is a normal domain: `IsDomain A ∧ IsIntegrallyClosed A`. Exact,
  using the dependency's prescribed domain specialization. The domain conjunct is
  stated by the node, despite also being a hypothesis.
- Explanatory conclusion every integral element of K belongs to A: read
  IsIntegrallyClosedIn, IsIntegrallyClosed and `isIntegrallyClosed_iff` in
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed. The latter identifies the
  second conjunct with `∀ {x : K}, IsIntegral A x → ∃ a, algebraMap A K a = x`.
  Exact; the explanatory clause is not an extra independent assertion.

Edge cases: zero x is outside the nonzero valuation criterion but belongs to A,
so is covered by the integral-closure conclusion. The zero ring is excluded by
IsDomain exactly as in the source. Fields, including finite fields and every
characteristic, are included. Non-Noetherian and higher-rank valuation domains
are included. Independent explicitly bound universes u and v restrict neither
ring nor fraction-field representation; there are no test-object quantifiers.
There is no index set or scheme in this item, so empty-index and empty-scheme cases
are inapplicable. Degree-zero monic integral equations are impossible in a field;
the docstring's multiplication argument includes degree one.

Independent searches (2026-10-11):

- msearch leanfinder, "A subring of a field containing either each nonzero element
  or its reciprocal is normal": eight hits, including ValuationSubring.ofSubring,
  ValuationSubring.mem_or_inv_mem and the ValuationRing instance on that subtype.
  Opened the relevant valuation-subring and valuation-ring sources.
- msearch loogle, "ValuationRing, IsIntegrallyClosed": two hits, both DVR TFAE
  theorems requiring Noetherian local domains; neither covers this node.
- msearch leansearch, "commutative domain with every fraction or its reciprocal in
  the image is integrally closed": unavailable (Internal Server Error); no verdict
  inferred from the unavailable service.
- rg of Mathlib valuation and integral-closure sources for IntegrallyClosed,
  ValuationRing, fraction, inv_mem and mem_or; rg of WeilConjectures and lean/Sheaf
  for valuation/normal combinations, inverse membership, the full declaration name
  and the blueprint id, and of dag/lean_names_upstream.json for the id. No exact
  declaration found. Read LocalSubring.mem_of_isMax_of_isIntegral (tag 00IC), the
  integrally-closed instances for ValuationSubring, and
  Valuation.Integers.isIntegrallyClosed: these concern a bundled local/valuation
  subring or a specified valuation and its integers witness. None has this node's
  arbitrary domain, fraction field and explicit criterion. Also read
  ValuationRing.iff_isInteger_or_isInteger: it gives the criterion equivalence,
  not the normality conclusion. They are tools for stage 3, not duplicate statements.

No semantic mismatch found; retained the Lean and node signature verbatim. No new
notion, node, dependency module or statement correction is needed. No hollow
definition exists (there are no definitions); the only theorem proof is `sorry`.
Both docstrings have the source and blueprint tag; the theorem docstring faithfully
carries all three node proof steps, including its final dependency. The sole import
provides the fraction-ring and integral-closure API used. All variables and universes
are explicitly bound, there is no private notation or instance, and all lines meet
the 100-character convention.

Second reading changed only the report: added this independent checklist, source
and API checks, additional searches, and clarified the dependency's current record.
The single-file server compile and delivery preflight are checked before pushing.
