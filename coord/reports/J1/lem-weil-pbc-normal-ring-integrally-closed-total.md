## Worker report

The module `Sheaf.RingTheory.NormalRingIntegrallyClosedTotal` states
`integral_totalFraction_mem_range_of_normal`, with its proof `sorry`. The node is
unchanged outside `lean`. There are no new notions, dependency modules, or statement
corrections. No statement dispute was found.

Hypothesis and clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`, with `universe u` explicit.
- R normal (`def-weil-pbc-normal-ring`): `hnormal : ∀ (p : Ideal R) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  This is precisely the dependency's Mathlib match, also the mandated inline form.
- S is the set of nonzerodivisors and Q(R) = S⁻¹R:
  `FractionRing R` unfolds to `Localization (nonZeroDivisors R)`.
  This is the ring case of `def-weil-pbc-module-localization`, not a second
  definition: Mathlib's `LocalizedModule.Basic` explicitly checks reducible equality
  of `Localization S` and `LocalizedModule S R` in
  `example_localization_eq_localizedModule` (lines 92–95). The ring version supplies
  the ring and algebra structure needed for the integral equation. A separate
  LocalizedModule import is unnecessary because the statement uses the ring version.
- Every element of Q(R): the arbitrary binder `(x : FractionRing R)`.
- Integral over R (`def-weil-pbc-integral-closure`): `(hx : IsIntegral R x)`.
- Lies in the image of the localization map: the conclusion
  `∃ r : R, algebraMap R (FractionRing R) r = x`.
- The equivalent phrasing “integrally closed in Q(R)” describes this same conclusion;
  no extra independent conclusion is omitted. The localization map is injective
  for localization at nonzerodivisors; `isIntegrallyClosedIn_iff` identifies
  `IsIntegrallyClosedIn R (FractionRing R)` with that injectivity and the elementwise
  conclusion above.

Dependency declarations read and used:

- `def-weil-pbc-normal-ring`: Mathlib match `IsDomain` (Mathlib.Algebra.Ring.Defs,
  class at line 439), `IsIntegrallyClosed` (Mathlib.RingTheory.IntegralClosure.IntegrallyClosed,
  abbreviation at line 74), `Localization.AtPrime`
  (Mathlib.RingTheory.Localization.AtPrime.Basic, abbreviation at line 57).
  The latter two modules are imported; they provide the normality hypothesis.
- `def-weil-pbc-module-localization`: `LocalizedModule`,
  Mathlib.Algebra.Module.LocalizedModule.Basic, with its docstring, `mk`, equality
  criterion, and `mkLinearMap` read. Its ring specialization is
  `Localization (nonZeroDivisors R)`, named `FractionRing R` in
  Mathlib.RingTheory.Localization.FractionRing (lines 708–717), transitively imported.
  The canonical ring localization map is `algebraMap`, sending r to r/1.
- `def-weil-pbc-integral-closure`: `integralClosure`, `IsIntegral`,
  `IsIntegrallyClosedIn`, per the recorded declaration list. Their signatures and
  docstrings were read in Mathlib.RingTheory.IntegralClosure.Algebra.Basic (216),
  Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs (53), and
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed (66).
  `IsIntegral` is used directly; the recorded `integralClosure` is the subalgebra
  with carrier `{r | IsIntegral R r}`. These modules are transitive dependencies of
  the imported IntegrallyClosed module.

Source checked: https://stacks.math.columbia.edu/tag/034M, Lemma 10.37.12 and its
proof. The cited local file `literature/stacks-project/algebra.tex` is absent on
this machine, so the official tag was read online. The theorem docstring contains
all three DAG proof steps, with the dependency ids; no proof is implemented.

Edge cases checked mathematically before writing:

- The zero ring: there are no primes, so normality is vacuous; FractionRing R is
  a singleton, and its unique element is in the localization map's image. No
  `Nontrivial R` hypothesis excludes this case.
- Normal rings with zero divisors, such as a product of two fields: the total
  fraction ring is the product of the fields, not a field. No `IsDomain R` or
  `Field (FractionRing R)` is imposed.
- An ordinary normal domain or a field: the same construction specializes to its
  field of fractions and gives the expected integral-closedness assertion.
- No Noetherian, finite-minimal-prime, characteristic, or local-ring restriction
  is added. The arbitrary universe u imposes no size restriction on R.

Searches (all msearch calls used the group J1 and this item; evidence is in
`searches.jsonl`):

- LeanSearch: “A commutative ring whose prime localizations are integrally closed
  domains is integrally closed in its total ring of fractions”. Service unavailable
  (Internal Server Error); no mathematical verdict is inferred from it.
- LeanFinder: “normal ring integrally closed in total ring of fractions”. Eight
  hits: `isIntegrallyClosed_iff_isIntegrallyClosedIn`, `isIntegrallyClosed_iff`,
  `isIntegrallyClosed_of_isLocalization`, and related ingredients. No exact theorem
  from prime-local normality for a general commutative ring.
- Loogle: `IsIntegrallyClosed, IsLocalization`. Six hits, including
  `isIntegrallyClosed_of_isLocalization`; none gives this implication.
- msearch grep: `of_isLocalization_maximal|isIntegrallyClosed_iff|normal.*ring`
  in RingTheory/LocalProperties. Eight hits. Read
  `IsIntegrallyClosed.of_isLocalization_maximal`: it requires `IsDomain R`, so it
  cannot be recorded as an exact match for this node.
- rg in the project's lean/Sheaf/RingTheory and in the read-only source's
  WeilConjectures/RingTheory for `IsIntegrallyClosed|normal.*ring|nonZeroDivisors`:
  normal-ring siblings and fraction-ring uses, no exact theorem.
- grep -rn of the item id in the source's WeilConjectures: no hit.
- rg throughout WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `integrallyclosed.*normal|normal.*integrallyclosed|integrally.closed.*total|total.*integrally.closed|integrallyClosed_of_normal`
  (case insensitive): normalization ingredients only, no duplicate declaration.

Validation: the file is submitted to `scompile.py` and the completed delivery is
checked with `deliver2.py --no-push`; the second reader will record their reading
and deliver. No second-reading claim is made by this worker.

## Second reading by J1

I independently opened the item's node, the delivered module, all three statement
 dependency nodes, and their Mathlib declarations. The statement agrees with
Stacks Tag 034M. The cited local Stacks checkout is absent here; I read the official
`algebra.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
labels `lemma-normal-ring-integrally-closed`, `definition-ring-normal`, and
`definition-domain-normal`, together with the chapter conventions. Those conventions
allow the zero ring and require commutative rings with identity. The normal-rings
section imposes no standing Noetherian or domain assumption on this lemma.

Object, hypothesis, and conclusion checklist:

- A commutative ring R: `(R : Type u) [CommRing R]`. PASS: arbitrary explicit
  universe, identity and commutativity, with no nontriviality restriction.
- R normal: `hnormal : ∀ (p : Ideal R) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  PASS: precisely `def-weil-pbc-normal-ring`'s accepted inline Mathlib match.
  `Localization.AtPrime` is localization at `p.primeCompl`; `IsDomain` supplies
  the nontrivial domain condition on each prime localization, not on R.
  `IsIntegrallyClosed` is closedness in that localization's fraction ring.
- S is the nonzerodivisors and Q(R) is S-inverse R: `(x : FractionRing R)`.
  PASS: Mathlib's `FractionRing` explicitly abbreviates
  `Localization (nonZeroDivisors R)` for arbitrary commutative rings. I checked
  `nonZeroDivisors` and its membership criteria. This is the ring specialization
  of `def-weil-pbc-module-localization`'s `LocalizedModule S R`; the private
  Mathlib example `example_localization_eq_localizedModule` verifies their
  reducible equality. It is not a field or a privately copied fraction ring.
- An arbitrary element x of Q(R), integral over R: `(x : FractionRing R)
  (hx : IsIntegral R x)`. PASS: `IsIntegral` uses a monic polynomial evaluated
  via the canonical `algebraMap`, as `def-weil-pbc-integral-closure` requires.
  The ring, normality, element, and integrality binders have the required order.
- x lies in the image of the localization map:
  `∃ r : R, algebraMap R (FractionRing R) r = x`. PASS: exactly elementwise
  membership, with no uniqueness or surjectivity assertion for nonintegral x.
  The canonical map sends r to r/1. Mathlib's `isIntegrallyClosedIn_iff` adds
  injectivity to this membership condition; `IsFractionRing.injective` already
  supplies that injectivity for localization at nonzerodivisors, without
  `[IsDomain R]`. Thus the node's equivalent closedness clause is fully covered.

Edge cases: PASS. The zero ring has no primes, so the normality binder is vacuous;
Mathlib provides `FractionRing.unique [Subsingleton R]`, and every total fraction
is the image of the unique ring element. A product of two fields is covered even
though it has zero divisors. Domains and fields specialize correctly. There is
no finite-minimal-prime, Noetherian, local-ring, or characteristic assumption.
There is no index family, scheme, or dimension parameter, so empty schemes and
n = 0 introduce no further case. All variables and the universe are bound.

Independent searches, recorded also in `searches.jsonl`:

- LeanFinder, “integral elements of localization at regular elements belong to
  locally integrally closed ring”: eight hits, including
  `IsIntegral.isAlmostIntegral_of_isLocalization`, `isIntegral_localization`,
  `isIntegrallyClosed_of_isLocalization`, and `IsIntegrallyClosed.of_localization`.
  None states the implication from normality at every prime for a general ring.
- Loogle, `IsIntegral, FractionRing`: zero hits.
- LeanSearch, “integrality in localization at nonzerodivisors follows from
  normality at every prime ideal”: service unavailable (Internal Server Error);
  no mathematical verdict inferred from this failed service.
- `rg` in Mathlib RingTheory, the whole upstream `WeilConjectures`, this project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, using
  `locally.*integrally|integrally.*locally|normal.*total|total.*normal`, plus
  `IsIntegrallyClosed.*AtPrime|AtPrime.*IsIntegrallyClosed` and the exact name:
  no duplicate. I opened the local-properties module and checked
  `IsIntegrallyClosed.of_localization`, `.of_localization_maximal`, and
  `.of_isLocalization_maximal`; each requires a domain R and cannot replace
  this statement. Project normality siblings conclude normality, not this
  total-fraction membership assertion.

No mismatch found; no module, signature, or node change was needed. There are no
new nodes, dependency modules, or statement corrections to review. Both imports
are used. The module and theorem docstrings cite Tag 034M and the blueprint id;
the theorem docstring contains each of the node's three proof steps, including
nonzerodivisor injectivity, passage to each prime localization's fraction field,
normality, denominator clearing, and the proper-ideal maximal-prime contradiction.
There are no definitions or hollow data, and the sole theorem proof is `sorry`.
The `lean.statement` is verbatim the file signature, with no unbound universe or
variable. Server `scompile.py` compiled the unchanged 49-line module in 1.4 seconds
with exit code 0 and no warnings. The completed report is checked by the delivery
dry run before pushing.
