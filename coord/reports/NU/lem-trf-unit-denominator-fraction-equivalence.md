# Stage-1 report: lem-trf-unit-denominator-fraction-equivalence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-unit-denominator-fraction-equivalence.json`: existing statement node, now split into six elementary steps; no exact Mathlib match for the complete statement.
- `citations.json`: the verbatim statement of `def-weil-field` supporting step 3.
- `searches.jsonl`: actual search log produced by msearch.py; existing searches in the copied item are retained, and five searches run by NU are appended to the node.
- `report.md`: this report.

No new nodes, no new Mathlib leaves, no unit changes, no Lean changes.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, unit-denominator terminology and fraction-field declarations. No project declaration states every clause of the item. Existing uses of IsFractionRing in other project theorems do not establish this statement.

## WANTED

None. The relevant ILO and Stacks sources are present.

## Findings and changes

The item is true as written; its statement and statement dependencies are unchanged. It already defines integral domain, unit and the fraction model inline, and cites the field definition. Its empty proof is replaced by the actual domain and fraction calculations. In particular the proof does not assume that B is a domain before establishing it, does not assume nonzero elements of A are units of B, and distinguishes those elements from the selected denominators whose images are units. Every nonzero element of A has nonzero image in B, and only becomes invertible after passing to Frac(B).

I read ILO VIII Lemma 3.2.9 and the first proof paragraph of Lemma 3.2.12, printed p.104, in the supplied PDF. They explain the common dense torus, generic comparison and monoid-algebra integrality motivating the extracted lemma. They do not state this abstract unit-denominator theorem. The proof is therefore marked agent-written, with the elementary fraction construction in Stacks Tag 09FJ (`fields.tex`, `example-quotient-field`) and the operations in Tag 00CO (`algebra.tex`, `definition-localization` and its preceding formulas) as its algebraic source. I also read Tag 00CP (`proposition-universal-property-localization`) but do not invoke its universal-property theorem: step 3 constructs the quotient map explicitly.

I read the live unit and chapter records, and the newest blueprint's unit, chapter and `lem-trf-local-term-locality.proof.md`. The historical ancestor's proof has since been replaced by the contracting-correspondence argument. The item's existing blueprint ancestry already calls its old toric branch historical. This delivery retains that provenance and proves only the existing abstract algebra item; it changes no geometric route and makes no assertion that the newest blueprint still needs this branch.

## Searches and Not duplicates

No new nodes were created. Whole-DAG searches for fraction fields, injective maps and unit denominators, and blueprint_refs searches for `fraction field`, `fraction`, and `unit denominators`, found no blueprint node stating this abstract equivalence with its explicit preimage formula. The ancestor command confirms `lem-trf-local-term-locality`; the existing from.place is specific and was retained, and same_as remains empty.

The copied item's earlier Mathlib records are retained as historical searches. NU ran LeanFinder with both the unit-denominator formulation and the more general localization formulation, LeanSearch with the unit-denominator formulation, Loogle for `IsFractionRing.map`, and grep in RingTheory/Localization for `def map |theorem map_|isDomain_of|of_field`. All services answered. The exact queries are recorded in searches.jsonl and mathlib_searches.

I read Mathlib/RingTheory/Localization/FractionRing.lean lines 409–422: `IsFractionRing.map` constructs a map but assumes B is already a domain and does not assert surjectivity. I read LocalizationLocalization.lean lines 278–289: `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` assumes an IsLocalization structure. The item's explicit denominator hypothesis must first supply additional arguments, so neither is a one-line match for the complete statement. The proof writes those arguments rather than creating nodes for these elementary consequences.

## Review by NU

I checked every step against the sources and against the item hypotheses. There are no new statements to review. For step 1 the only inputs are injectivity, preservation of 0 and 1, and the definition of an inverse; this proves B is nonzero before claiming a unit is nonzero. Step 2 multiplies the two selected denominator equations, uses injectivity to obtain ab=0 in A, and uses the two actual inverse units to deduce x=0 or y=0. It needs no localization theorem and no unproved descent of domains.

Step 3's only cited node is `def-weil-field`. I opened its statement: it says exactly that a field is nonzero and every nonzero element has an inverse. The quote in citations.json copies its complete statement, not a universal property absent from that definition. The fraction representation, equality criterion and operations used by the step are already part of the item statement; Tag 09FJ confirms the same model. Injectivity of k is the equality criterion with denominators 1. The step writes out well-definedness and the sum/product formulas, rather than relying on an uncited existence theorem for J. Step 4 again uses only the cross-product criterion and injectivity of i; no general theorem about field maps is invoked.

Step 5 uses arbitrary witnesses a,s,b,t, not specially chosen or unique denominators. It checks s and b are nonzero before forming (ta)/(sb), deriving b nonzero specifically from y nonzero and the unit i(t). Its displayed calculation proves the exact formula for every such witness. Since the fraction representation is part of the definition in the statement, this also proves surjectivity. Step 6 packages the bijective ring map and explains why its inverse preserves operations; the extension property was already computed at a/1. Steps 1, 2, 4, 5 and 6 cite no nodes because their full arguments are elementary from the hypotheses and definitions. No step conceals a comparison or standard lemma, and the longest step is 592 characters.

For edge cases I checked A=B with i the identity, a field A with B=A, Z contained in Z[1/2], and Z contained in Q. The formula is the identity on their common fraction field. The case x=0 gives numerator a=0 by injectivity and remains valid; y=0 is explicitly excluded. A zero chosen denominator cannot have unit image, since B was proved nonzero first. The zero ring B cannot satisfy injectivity from the nonzero domain A. A=k contained in k[epsilon]/(epsilon^2) fails the denominator hypothesis for epsilon, explaining why mere injectivity would not prove the domain clause. Thus no missing domain or nontriviality assumption is being supplied silently.

Against delivery-errors B–E, I checked the complete statement introduces its objects, TeX uses single mathematical escapes, every definition used is inline or the cited field node, and every source tag matches the local label. There are no new-node forms, duplicate tags or Mathlib leaf claims. The proof contains the argument itself rather than restating clauses in auxiliary nodes. Its only dependency is the existing Mathlib field-definition leaf, so it creates no cycle or off-unit theorem dependency. No statement dispute or source correction is needed.

## Unfinished work

None in this one-level stage-1 split. Maintainer review and any later Lean formalization remain outside this delivery.
