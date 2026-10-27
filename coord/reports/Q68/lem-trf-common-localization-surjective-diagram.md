# Worker report: lem-trf-common-localization-surjective-diagram

## Files written

- dag/nodes/sec-trace-formula/lem-trf-common-localization-surjective-diagram.json: existing statement split into six steps; no exact whole-statement Mathlib match.
- citations.json: eight literal quotations, one for each step/node citation.
- searches.jsonl: five new searches actually run with msearch.py, all services available.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The three reused dependencies are existing Mathlib leaves.

## Attachments

None. Searched the live lean/WeilConjectures source for the exact blueprint tag and the common-localization and surjective-local-map notions. The common-localization hits concern chart overlaps or unrelated constructions; the localRingHom hits concern maps between two prime localizations, not all the clauses of this item. No exact declaration was found.

## WANTED

None.

## Findings and changes

The statement is correct as written and is preserved verbatim. Its source field, created record, chapter, unit, blueprint provenance and earlier Mathlib search records are preserved. The empty proof is replaced by explicit arguments; proof_deps is precisely their citation union. The existing blueprint.from.place was already specified. same_as remains empty after whole-blueprint searches for common prime, unit denominator and 00CP. The current latest blueprint is snapshot main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345. I read its sk-i-curve-zero section and lem-trf-local-term-locality statement and proof, as well as the DAG chapter/unit records and the parent split. This item is the supporting local algebra already identified in the inherited provenance, not a replacement for a unit step.

The Mathlib search hits were read, especially IsLocalization.lift, lift_mk', lift_eq, ringHom_ext and lift_surjective_iff in Localization/Defs.lean (488, 507, 517, 543, 573), IsLocalRing.notMem_maximalIdeal in LocalRing/MaximalIdeal/Basic.lean:83, IsLocalHom.of_surjective in LocalRing/RingHom/Basic.lean:118, and RingHom.surjective_localRingHom_of_surjective in RingHom/Surjective.lean:88. The semantic search also returns RingHom.surjective_localRingHom_iff in SurjectiveOnStalks.lean:44. These facts apply to single induced maps or assume an already-surjective source map; none is a one-line specialization giving this entire common-prime diagram. The relevant general universal property and unit criterion already have DAG leaves, so no new Mathlib leaf is needed. I tried a second semantic phrasing. Every appended record reproduces the tool/query and actual logged response; the inherited records remain intact.

## Not duplicates

No new nodes. Reused lem-weil-pbc-ring-localization-universal-property instead of creating a second 00CP node; reused lem-weil-pbc-local-ring-unit-criterion instead of creating a second 00E9 node. Prime preimages, diagram equalities, fraction witnesses and maximal-ideal images are elementary steps, not new nodes or restated clauses placed in children.

## Review by Q68

I read Stacks algebra.tex at Proposition 00CP (proposition-universal-property-localization), its proof giving the formula and uniqueness, Lemma 00E9 (lemma-characterize-local-ring), Definition 07BI (definition-local-ring) and the following prime-localization paragraph, and Lemma 07BJ (lemma-characterize-local-ring-map). I checked tags against stacks-project/tags/tags; this corrected a draft reference that called the local-map lemma 00EA. No SGA source is used. There are no new-node sources to audit.

Step 1 uses only the unit-criterion node. I opened its complete statement: it supplies both implications between being a unit and being outside the unique maximal ideal. Locality supplies one inclusion; applying the ring map to an inverse supplies the converse. Both P and Q and the common target A are local by hypothesis. Surjectivity is not needed for this step, so none is assumed for f or g.

Step 2 again uses exactly that unit criterion for A. I wrote the ideal and properness check and proved primality by multiplying h(a)h(b) in the maximal ideal by the inverse of h(a). This avoids silently importing a maximal-is-prime or prime-comap theorem. The complement is multiplicatively closed by that explicit prime condition.

Step 3 cites the prime-localization definition, the unit criterion and the general localization universal property. I opened all three statements. The definition supplies D_n and its canonical map. Step 1 ensures every denominator has unit image in each target, which is the precise hypothesis of the universal property. That node explicitly supplies existence, uniqueness and the fraction formula, so no content is taken just from its proof. All eight citations in the six steps are backed by the relevant statements verbatim in citations.json.

Step 4 uses the uniqueness clause, whose statement explicitly says that two homomorphisms from the localization agreeing on D are equal. I wrote both precomposition equalities, rather than merely saying compatibility is transported.

Step 5 uses the unit criterion to place each supplied denominator outside n. The two fraction equations in the hypotheses then produce explicit preimages under alpha and beta. The earlier established formula and diagram are used from steps 3 and 4. Surjectivity of u, which really is a hypothesis, gives a preimage in P for each element of A; composing preimages proves gamma surjective. No surjectivity of h is asserted. Surjectivity of v is redundant but remains a hypothesis of the unchanged statement.

Step 6 cites the prime-localization definition's explicit assertion that the maximal ideal of T is nT. I wrote its finite-sum expression and checked the image of every generator under each of the three maps. Closure of an ideal under sums and scalar multiplication proves locality directly; no unrecorded theorem about surjective local maps is needed.

I checked delivery-errors B through E. There is no new statement-only child to be circular, duplicate, elementary, or a restated clause. The six steps are between 248 and 605 characters, and no long step conceals an auxiliary lemma. No Noetherian, completeness, regularity, domain or injectivity assumption is used. The fraction argument works with zero divisors: it multiplies only units, never cancels a nonunit. For fields P=Q=A=k and D=k[x] mapping by x to zero, n=(x), and k[x]_(x) maps surjectively to k exactly as claimed. For P=Q=k[e]/(e^2), A=k and D=P, with quotient u=v and identity f=g, the construction is the identity localization and the residue map; nilpotents cause no failure. Zero rings cannot satisfy having exactly one maximal ideal; D=0 cannot map unitaly into the nonzero A. Taking D=Z, P=Q=A=Z_(p) tests that the original maps f,g,h need not be surjective, whereas their localization extensions are. These checks required no statement correction.

The three proof tools are existing Mathlib leaves, so their different unit does not change the route. Only the item, report, literal citations and genuine search log were written, all in the authorized sandbox. No Lean was written and no compiler or build was run.

## Unfinished work

None in the mathematical split. Required server dry run and direct push follow; their outcomes are recorded below.
