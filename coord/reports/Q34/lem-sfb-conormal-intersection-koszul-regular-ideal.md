# Worker report — Q34

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-conormal-intersection-koszul-regular-ideal.json` (statement, split; no Mathlib match), `citations.json`, and this report. No new nodes, no new Mathlib leaves. `searches.jsonl` was produced by the authorized search command. The item retains its statement, statement dependencies, inherited source, creation record and blueprint fields.
2. Attachments: none. Searching the exact blueprint tag and the conormal-intersection notion in `lean/WeilConjectures/` found no exact declaration. `Ideal.inf_sq_eq_mul_of_regular_quotient` in `RingTheory/ConormalIntersectionRegularQuotient.lean:37` assumes a global classical regular sequence; it does not cover locally Koszul-regular generators over arbitrary rings.
3. WANTED: none.
4. The item had no proof. Its cited Stacks result is correct, but “by localizing” in 07CX needed expansion. A global H1-regular quotient identity already exists, so making another local algebra node would duplicate work. The imported unit record and latest blueprint route differ in presentation; neither is changed. The inherited blueprint ancestor is null (confirmed by `blueprint_refs.py ancestor`); its exact existing place and via chain are retained. This split supplies only the local algebra input of the direct-image chain, not a new route for the unit.
5. Unfinished: none in this one-level split. The reused global H1 node remains a separately queued statement, as intended by stage 1.

## Searches and reuse

Read the current item and its inherited Mathlib search results. Ran five additional logged queries with msearch.py: LeanFinder twice with different formulations, Loogle, grep in RingTheory, and LeanSearch. All services responded. Read the only Loogle candidate, `injective_lTensor_quotient_iff_inf_eq_mul` at Mathlib/RingTheory/Ideal/Pure.lean:43: this characterizes tensor injectivity and does not provide it from Koszul regularity. The other hits give cotangent quotient identities, ideal arithmetic, coprimality or Dedekind specializations. No exact or one-line Mathlib specialization was found. Query text and results are recorded in the item; the grep subdirectory is recorded in its result and in searches.jsonl.

Searched the whole DAG by 07CX, conormal-sequence-H1, and Koszul syzygy/relation concepts, and the whole blueprint by 07CX, conormal intersection, Koszul-regular and H_1-regular. The blueprint searches returned no matching imported nodes. Existing `lem-sfb-h1-regular-quotient-ideal-intersection` (Stacks 0666) is precisely the required globally generated chart case. Reused the two existing Mathlib leaves for quotient-localization and membership detection. No new node ids or duplicate-tag comparisons arise.

## Not duplicates

lem-sfb-conormal-intersection-koszul-regular-ideal vs lem-sfb-h1-regular-quotient-ideal-intersection: the item assumes Koszul-regular generators on neighborhoods of primes of T/L; the reused lemma assumes global H1-regular generators in the quotient. The item's localization argument is the extra content.
lem-sfb-conormal-intersection-koszul-regular-ideal vs lem-weil-pbc-conormal-intersection-regular-quotient: the latter assumes a global classical regular sequence, a stronger hypothesis than the item has. It cannot replace the local Koszul-regular assertion.

## Review by Q34

I read more-algebra.tex, definition-regular-ideal, Tag 07CX (lemma-conormal-sequence-H1-regular-ideal), and its cited Tag 0666 (lemma-conormal-sequence-H1-regular), including the proof through 0665. The item's explicit neighborhood hypothesis is exactly the Koszul-regular-ideal clause of that definition. All positive homology vanishing includes degree one, so 07CX applies without any extra Noetherian or flatness condition. I also read algebra.tex Tag 00CT (proposition-localize-quotient), the fraction convention in 00CO, and Tag 00HN (lemma-characterize-zero-local). The latest blueprint's direct-image proof (3) and unit text were read; the supporting local algebra stays on the inherited route.

For steps 1–2 I checked the elementary inclusions and the case K not contained in a maximal ideal. In that case xk is an actual element of LK and the denominator k is invertible. These steps require no non-elementary fact and cite no node.

For step 3 I opened the entire statements of `lem-weil-pbc-localization-quotient-commute` and `def-weil-pbc-koszul-regular-sequence`. The former gives the exact ring isomorphism needed with B=T, J=L, b=t, including its formula on fractions; it is not merely module exactness. The latter explicitly defines H1-regularity by H1=0. The inverse image of m/L is m, so the chosen lift t is outside m. Identifying the quotient via that isomorphism is only a change of the coefficient-ring presentation. Each f_i lies in the image ideal J/I, so it has a lift inside J, not merely inside A. No localization-preserves-Koszul-homology theorem is being assumed: the supplied sequence is used on its given chart.

For step 4 I opened `lem-sfb-h1-regular-quotient-ideal-intersection` and checked its full statement: A is any commutative ring, I is contained in J, the finite sequence lies in J, its images generate J/I, and H1 vanishes. Those are exactly the objects established in step 3. Its conclusion I intersection J squared = IJ is verbatim in citations.json. Extension commuting with ideal products is expanded by their generators, so no unrecorded flatness or intersection-localization theorem is used.

For step 5 I opened `def-weil-ring-localization-away`; its equality-of-fractions clause supplies the extra power t^q needed after clearing the finite collection of denominators. The proof writes out the numerator b and establishes t^(N+q)x in LK. It does not infer t^Nx=b in T from equality in a localization. This last distinction was explicitly checked against delivery-errors E5.

For step 6 I opened `lem-weil-pbc-ideal-membership-at-maximal-localizations`. It states the exact elementwise membership implication for every maximal localization, with no finite-generation hypothesis. Applied to the ideal LK it closes the argument. Both external-unit statement tools are already Mathlib leaves, and the H1 statement has this item's unit, so no off-route tool declaration is needed.

I checked delivery-errors B–E: no new-node schema or new-statement issues arise; the existing item keeps its notions and TeX; every non-elementary fact is one of the cited statements just read; the proof is the local-to-global argument rather than a replacement name for the whole item; all five citations are literal substrings of those statements. No new proof dependency points back to this item. All steps are below 2000 characters. I removed a forward bracket citation to the H1 lemma from the hypothesis-verification step so that uses and actual citations agree; the actual application is in step 4.

The edge cases were checked directly: K=L gives L squared on both sides, L=0 gives zero, K=T makes the neighborhood condition vacuous and gives L on both sides, the zero ring gives zero, and an empty local sequence gives J=I and I intersection I squared = I squared = IJ. No argument excludes any of these. No statement dispute or source error was found, and no Lean file or compiler was used.

## Validation

The first dry run rejected the short displayed-equation quotation for step 4 (the citation gate requires at least 40 characters). Replaced that quote by the entire existing H1 statement, including all hypotheses and the conclusion. The mathematical proof and statement were unchanged.
