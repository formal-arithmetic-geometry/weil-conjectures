# Stage 1 report: `lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z`

## Worker report

The item is split into four proof steps. Its statement was changed only by
expanding "local ring" to "a commutative ring with exactly one maximal ideal
\(\mathfrak m\)"; all quantified data and both conclusions are unchanged.
Stacks Algebra Lemma 00QU (`lemma-limit-essentially-finite-type`, proof's
second and third paragraphs) chooses the finite subsets of `R`, takes their
generated sub-`Z`-algebras, localizes at the traces of the maximal ideal,
and asserts their colimit is `R`. Lemma 00QT uses the same base-ring
construction. Thus the item is exactly the base-ring part of 00QU, with its
commutative-ring colimit and essential finite-type conclusion made explicit;
it does not claim the accompanying approximation of `S`.

Step 1 cites `def-weil-pbc-localization-at-prime` for the local ring
`R_A=(Z[A])_(Z[A] cap m)` and its maximal ideal,
`def-weil-pbc-finite-type-algebra` for finite generation of `Z[A]`, and
`def-weil-pbc-essentially-finite-type-algebra` for its localization. The
finite-subset poset is inhabited by the empty set and directed by union;
the trace of `m` is prime because `m` is maximal. Step 2 uses the localization
definition's fraction equality to construct the transition maps, checks
locality via the traced ideals, and checks identities and composition by the
same fraction formula. Step 3 uses the new unit-criterion leaf to invert
every denominator in `R`, and the localization definition to show the maps
`R_A -> R` are well defined, local, compatible, and injective. In particular,
injectivity does not assume `R` is a domain: equality of images gives
`at-bs=0` already in the subring `Z[A]`, and witness `1` proves equality of
fractions. Step 4 uses `def-weil-pbc-category-colimit` and verifies its
universal property: every element is represented at `{x}`, two
representations agree after passing to `A union B` by injectivity, and the
ring operations and uniqueness follow at a common index. These steps spell
out the "clear" colimit claim in 00QU and the omitted details in 00QT.

The only new node is
`dag/nodes/sec-proper-base-change/lem-weil-pbc-local-ring-unit-criterion.json`,
a self-contained, statement-only Mathlib leaf for a commutative local ring:
an element is a unit exactly when it lies outside its unique maximal ideal.
Its source is Stacks Algebra 00E9 (`lemma-characterize-local-ring`, clauses
(1) and (3)). Mathlib's `IsLocalRing.notMem_maximalIdeal` states
`x \notin maximalIdeal R <-> IsUnit x` at
`Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean:83`; the docstring and
statement were read at lines 79-84. Applying it to `R` is one specialization.
The node has empty proof and proof dependencies, cites its source by tag and
label, and records LeanSearch, LeanFinder, and source-grep searches. Its
`created.item` is this item.

I searched the whole imported blueprint for "local ring colimit",
"localization at maximal ideal", "local ring unit", "unit criterion", and
"maximal ideal", and searched DAG nodes by the 00QU/00E9 notions; no
blueprint node states either new fact. The item's `blueprint.from` traces
through `lem-weil-pbc-limit-tower-essentially-finite-presentation` to step 7
of `thm-weil-pbc-finite-etale-lifting`, where this base-ring approximation is
used. The split preserves that route. In read-only
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, searches for both exact
`(blueprint: <node id>)` tags and the local-ring colimit notion found no exact
declaration. `CommRingCat.isColimitFgSubalgebraCocone` (file
`Mathlib/Algebra/Category/Ring/FilteredColimits.lean:136`) handles finitely
generated subalgebras without the localizations, while
`CommRingCat.isColimitAwayProdCocone` (same file, line 234) handles one prime
localization. Neither states the item's combined system, so there is no Lean
attachment, with or without sorry. No source is WANTED.

Edge cases checked: `A=empty` still supplies an index and a localization of
the prime subring image; a field `R` has `m=0` and the construction still
works; zero divisors in `R` are handled by the fraction equality witness;
`R=0` is excluded by the hypothesis of exactly one maximal ideal. The new
unit statement holds in a field (`m=0`) and in a non-domain local ring such
as `k[epsilon]/(epsilon^2)`. No cross-unit tool is used.

`python3 tools/review_split.py lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z`
passes and reports one new node. `python3 tools/check_dag.py` reports zero
cycles and seven pre-existing reachability warnings unrelated to this item.
Both edited JSON files parse. No Lean was written or built.

## Review by C1

Preflight found two missing metadata fields in the new leaf. I added `mathlib_match.line = 83` after reading the pinned declaration and cited `def-weil-pbc-depth`, whose statement explicitly defines a local ring as a commutative ring with one maximal ideal. The mathematical statement is unchanged.

I read Algebra 00QU (`lemma-limit-essentially-finite-type`), its finite-subset construction and colimit assertion, 00QT for the same base system, and 00E9 for units in a local ring. The item statement only makes the meaning of local ring explicit; it retains the colimit and essentially-finite-type conclusions of the base-ring portion of 00QU. Step 1 uses the localization-at-prime, finite-type, and essentially-finite-type definition nodes exactly for their statements. Step 2 checks the transition map's denominator condition and fraction equality, and locality by traced maximal ideals. Step 3 uses the new unit criterion leaf for denominators outside m; injectivity follows because equality in R is equality in the subring C_A and witness 1 works in its localization, even with zero divisors. Step 4 checks the commutative-ring colimit universal property at A union B, including uniqueness. I tested A empty, R a field, and a non-domain local ring; R=0 is excluded by its unique-maximal-ideal hypothesis.

The new child is a self-contained, statement-only Mathlib leaf. I read pinned `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean:79-84`: `notMem_maximalIdeal` states exactly nonmembership iff unit, and its source is Algebra 00E9 with the correct label. Its definitions, source, searches, and blueprint chain were checked; DAG and whole-blueprint searches found no duplicate. The read-only slopmaster2 source has separate finite-subalgebra and localization colimits, not this combined local system. The worker added the missing external report after my request. `review_split.py` passes and `check_dag.py` has no cycles, only seven unrelated existing reach warnings. Sections A-E of `coord/delivery-errors.md` are satisfied.
