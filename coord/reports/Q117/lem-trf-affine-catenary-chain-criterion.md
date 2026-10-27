# Stage-1 report: lem-trf-affine-catenary-chain-criterion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affine-catenary-chain-criterion.json: statement, split; no complete Mathlib match. Preserved the statement, original searches, source, blueprint ancestry and provenance; added seven proof steps and the searches actually run by Q117.
- citations.json: one verbatim statement quotation for each cited node in each step.
- report.md and searches.jsonl: review and actual search log.

No new nodes; zero new Mathlib leaves. Reused the existing Mathlib leaves lem-weil-pbc-affine-open-spec-points and lem-weil-pbc-spec-irreducible-closed-subsets-primes.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, catenarity, and saturated/irreducible-chain terminology. RingTheory/Excellent.lean defines IsCatenaryRing (lines 44–52) but does not prove the item's affine topological equivalence or interval correspondence. Thus it is not an attachment. Its bounded-chain definition agrees with the node.

## WANTED

None. All sources used are present.

## Issues and corrections

The imported item was statement-only and already correctly included bounded lengths, the entire interval, saturation, and the empty affine scheme. No statement correction or route change was necessary. The source's word “Immediate” in algebra.tex Tag 02IH was expanded into actual constructions and inverses. Saturated-chain existence uses a greatest attained finite length, not a finiteness or Noetherian hypothesis on the interval. No new lemma merely restates an item clause.

The affine presentation and prime/irreducible correspondence already exist as Mathlib leaves; searches of the DAG and blueprint found these, so creating duplicates would have been wrong. Blueprint searches for catenary, affine scheme, and irreducible closed were read; no imported blueprint node states the complete item. The existing ancestry and precise from.place were retained. This is an inherited excellence-locality tool below lem-trf-local-term-locality, not a replacement for the contracting-local-term route.

## Not duplicates

No new nodes. Reuse of the two existing leaves eliminates the possible duplicate affine reconstruction and spectrum-order-duality nodes.

## Review by Q117

I read algebra.tex Tag 02IH (lemma-catenary), including its proof referring to lemma-irreducible; Tag 00ES (lemma-irreducible), statement and proof; and Tag 00NI (definition-catenary). I verified their labels in stacks-project/tags/tags. I also read schemes.tex Tag 01HW (definition-affine-scheme), the full statement and Mathlib record of the affine-open presentation node, and the full statements of both definition nodes cited below. There are no new nodes requiring additional source review. The Mathlib spectrum order equivalence was read in RingTheory/Spectrum/Prime/Topology.lean lines 967–983. Upstream RingTheory/Excellent.lean lines 44–52 confirms the bounded finite-chain and cover-chain convention.

Step 1 uses lem-weil-pbc-affine-open-spec-points exactly as stated: take the affine open U to be the whole affine scheme T. Its statement explicitly supplies the isomorphism U to Spec of its own section ring, not merely a morphism or a pointwise surjection. The underlying isomorphism gives h. No nonempty hypothesis occurs.

Step 2 uses def-weil-irreducible-components for nonemptiness and the closed-decomposition definition. Images and inverse images under mutually inverse continuous maps preserve closed sets, inclusions and nonemptiness. The text explains the closed-decomposition argument in both directions; this is elementary and requires no independent homeomorphism-invariance lemma.

Step 3 uses the actual statement of lem-weil-pbc-spec-irreducible-closed-subsets-primes: clause (2) gives existence and uniqueness for every irreducible closed subset, and clause (1) gives the reversed inclusion criterion. These two assertions give F globally, and the two interval inequalities restrict it to all intermediate members. The cited statement concerns arbitrary commutative rings, so no Noetherian, domain, or nonzero hypothesis is being supplied silently.

Step 4 uses the already constructed bijection. The explicit reversed list and its inverse preserve the number of strict inclusions. The correspondence between an insertable closed subset and an insertable prime proves saturation in both directions, rather than assuming that a selected chain controls the whole interval. Step 5 is finite combinatorics: the attained lengths lie in the finite natural-number interval from zero to N and include at least one length. The greatest attained length is realized by definition, and an insertion contradicts its maximality. No unproved assertion about maximal chains is used.

Step 6 reads the catenarity clause in def-exc-excellent-ring, whose statement explicitly includes both bounded finite-chain lengths and equality of saturated-chain lengths. That clause defines catenarity; the proof does not assert that R is excellent or universally catenary. The globally bijective F means every irreducible-closed endpoint pair is covered, so the interval equivalence proves both quantified implications. Step 7 checks the sheaf empty-cover axiom, the zero ring's absence of proper prime ideals, and the nonemptiness built into irreducibility. Hence the empty case is vacuous without invoking a false nonzero-ring convention.

I checked B1–B10: no new nodes, notions are cited, TeX is singly escaped, exact source labels are recorded, and all appended searches were executed through msearch.py and read. LeanFinder was tried with two different mathematical questions; its dimension and flag hits are not the whole criterion. Loogle's spectrum correspondence is already the reused leaf; the Mathlib grep had no catenarity hits; LeanSearch returned affine and dimension-related declarations, not the criterion. Existing search history is preserved.

I checked C1–C8: every non-elementary input is a cited existing statement, and each was opened and quoted verbatim in citations.json. Proof dependencies are exactly the union of uses. Only existing Mathlib statements and definitions are used, so there is no new off-route statement tool, no cycle introduced through a new child, and no use of another node's proof in place of its statement. D1–D5 are met by the actual interval/chain argument, without relabelled clauses or circular citations. E1–E7 were checked on equal endpoints, a field, a discrete valuation ring's two-point prime interval, and the zero ring. In each case chain lengths and their reversed images agree. No source error was found. Each step is below 700 characters, so none conceals a long subsidiary argument.

## Repair of the returned delivery

The return dated 2026-10-22 14:35 UTC names head b9fc5ccf894 and says that the reader approved the mathematics but the side completion was not promoted into the live DAG. I continued the retained delivered files. Before editing, I verified that the item, report, citations and search log have exactly the input hashes of the previous durable delivery receipt (head 5bdc4897595); no earlier proof or searches were discarded. The first required dry run repackaged that retained content on the current server DAG and passed at bf99a371313.

I compared the retained node with the current read clone. The live item is unsplit, with no proof; statement, statement dependencies, source, chapter, unit, creation record and blueprint ancestry are identical. The differing fields are exactly the retained split's proof, proof dependencies, proof origin, status, split report and appended Mathlib searches. Thus this delivery supplies the missing live split, rather than treating the side completion as a finished live node. The delivery tool builds its commit on the freshly fetched origin/sheaf-dag and preserves maintainer metadata.

I reopened every cited node in the current DAG: lem-weil-pbc-affine-open-spec-points still gives the affine isomorphism, def-weil-irreducible-components still gives nonempty irreducibility, lem-weil-pbc-spec-irreducible-closed-subsets-primes still gives both uniqueness and reversed inclusions, and def-exc-excellent-ring still defines the required two chain conditions. Every saved quote remains a verbatim part of the current statement. No citation needs replacement or additional hypotheses.

The repaired Step 4 now explicitly checks that every candidate insertion lies in the full endpoint interval before invoking its bijection; this ensures saturation is tested against all intermediate objects. The repaired Step 6 explicitly distinguishes the unrestricted catenary chain definition from the Noetherian qualification of universal catenarity. I reread Stacks algebra.tex Tags 00NI, 02IH and 00ES and schemes.tex Tag 01HW, and checked equal endpoints, a field, a DVR and the empty affine scheme again. The source route and statement are unchanged, so the recorded Mathlib queries and their read results are reused without repeating them. No new nodes or leaves are needed. This paragraph supplements my Review by Q117 above and addresses the sole return point.

## Unfinished work

None within this one-level split. The independent maintainer review remains part of the delivery protocol.

## Repair rebase checked on 2026-10-23

I continued the retained delivery described above, including its earlier repair history, rather than copying the unsplit live item over it. The required first dry run exited successfully at 24bcaea6dd1 on the freshly fetched server DAG. In the current read clone the item remains unsplit. Comparing its fields with the retained delivery shows that the statement, statement dependencies, source, chapter, unit, creation record and blueprint ancestry agree; the differences are the proof, proof dependencies, proof origin, status, split report and appended searches. The delivery tool rebases precisely these owned fields while preserving current maintainer metadata. This addresses the returned landing's missing live promotion; the old side completion is not used as evidence that the live node is complete.

I reopened all four proof citations, including the current complete catenarity clause of def-exc-excellent-ring, and both other statement-definition dependencies. All four entries in citations.json remain verbatim substrings of the current statements. Step 1's affine-open statement supplies the actual affine isomorphism. Step 2's irreducibility definition supplies nonemptiness and the closed-cover test. Step 3's spectrum statement supplies uniqueness and inclusion reflection, with no Noetherian hypothesis. Step 6 uses only the catenary clause; the Noetherian qualification applies to universal catenarity. No cited statement required replacement.

As a concrete repair refinement, Step 3 now applies the inverse to an arbitrary member of the closed-subset interval and checks both prime-interval inequalities separately. Step 4 now gives both indexed chain formulas and verifies that they are inverse, including the singleton chain. Its saturation argument still tests every insertion from the whole interval. These edits preserve every argument in the approved split and make the rechecked interval correspondence explicit. Steps 5 and 7 remain the elementary maximum-attained-length argument and the empty-cover/zero-ring argument. I reread the local Stacks statements and proof at Tags 02IH, 00NI and 00ES, and the affine-scheme definition at 01HW; their route and hypotheses agree.

I rechecked B through E against this version: no new nodes or restated clauses, no unstated non-elementary input, no changed hypotheses or source route, and exact proof-dependency union. Equal endpoints give length zero, a field has only that case, a DVR's distinct endpoint chain has length one, and the zero ring has no prime interval. All seven proof steps remain shorter than 2000 characters. The recorded search results and search log have been read and retained, since neither the statement nor the search questions changed. The new source search still finds only the IsCatenaryRing definition and unrelated chain lemmas, with no complete project attachment. No Lean file was written and no compiler was run. This recheck supplements my signed Review by Q117 above.
