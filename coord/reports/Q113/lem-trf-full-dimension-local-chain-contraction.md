## Files written

- `dag/nodes/sec-trace-formula/lem-trf-full-dimension-local-chain-contraction.json`: item, statement unchanged, four proof steps; not a Mathlib leaf as a whole.
- `citations.json`: verbatim statements for every proof-step citation.
- No new nodes; no new Mathlib leaves. `searches.jsonl` records the searches run by the prescribed command.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for local prime-chain contraction and dimension/height terminology. The filtered-colimit contraction declarations concern a different ring construction; the finite-type-domain chain declarations require finite type over a field, absent here. No project declaration supplies this item's full assertion for an arbitrary domain and every optimal local chain.

## Literature wanted

None.

## Corrections and route

The statement is correct and has not been changed. The imported node had no proof. Read the current main-20261015 blueprint proof of `lem-trf-local-term-locality`, paragraphs (1)--(2), to retain the normal-cone specialization ancestry. This elementary commutative-algebra auxiliary serves the alteration-dimension input through the already recorded intermediate nodes, rather than changing any unit-level route. Stacks Algebra Tag 00E3, `lemma-spec-localization`, proves the prime correspondence; Algebra Tag 00KE, `definition-Krull`, supplies the supremum definition; Morphisms Tag 02JX, `lemma-alteration-dimension`, equality proof, explains the local-dimension prime-chain use. The finite-supremum and endpoint arguments are written out by this worker, so proof_origin is agent rather than claiming the literal proof is in Stacks.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-primes-of-localization` (Mathlib, clause (1)) rather than creating another Tag 00E3 node. Reused the existing Krull-dimension definition. The existing localization-dimension-chains-below-prime node is unnecessary once the actual prime correspondence is used. Blueprint searches for prime chain(s), localization, and maximal ideal found no equivalent imported statement; `same_as` stays empty. Whole-DAG searches included Tag 00E3, localization/prime correspondence, chain contraction and dimension-chain file names.

## Review by Q113

I read delivery-errors B--E and checked the four steps against the actual statements, not their proofs. For step 1, `def-weil-pbc-krull-dimension-ring` explicitly defines dimension as the supremum of integer lengths and explicitly gives dimension -infinity for an empty prime spectrum. Thus a finite nonnegative supremum is attained: for positive r use the upper bound r-1 if r is missing, and for r=0 use the empty-spectrum clause. This uses discreteness of integer lengths, not an unquoted chain-attainment theorem.

For step 2 I opened `lem-weil-pbc-primes-of-localization` and read clause (1): it gives exactly contraction as an inclusion-preserving bijection to primes below the chosen prime, with inverse extension. The ring in that statement is instantiated with the item's A and its prime with the item's maximal ideal m. I included the two-line proof that m is prime, so no implicit hypothesis is added. Injectivity of this bijection gives strictness after contraction; ordinary inverse images preserve inclusions. I also read Stacks algebra.tex at `lemma-spec-localization` and its extension/contraction proof, and Mathlib's AtPrime/Basic.lean orderIsoOfPrime and primeSpectrumOrderIso declarations. This existing Mathlib leaf is a generic algebra tool, exempt from unit-route restrictions.

For step 3 the nonzero-domain hypothesis makes (0) a proper prime ideal directly from the definition, written in the step. The contracted chain consists of primes by step 2, so if its first prime is nonzero prepending (0) really adds one strict inclusion. The same Krull-dimension definition bounds its length by dim A=r, giving the contradiction. No localization-injectivity or minimal-prime theorem is silently invoked.

For step 4 the final prime is below m by step 2, and m is prime by the explicit argument there. Appending m when the inclusion is strict again adds exactly one to the length and contradicts dim A=r. This proves the conclusion for every optimal chain, not just a specially chosen chain. Both endpoint arguments work for a singleton chain at r=0, and give m=(0); for a field they reduce to its only prime, and for A=Z at (p) they give the familiar (0) < (p). No Noetherian, catenary, finite-type, or field hypothesis is used. The zero ring is excluded by the item. Finite dimension is essential for the length-r and length-(r+1) comparison.

I read all Mathlib search hits. They give the prime correspondence, height/dimension identities and a chain realizing finite height, but no single theorem (or one-line specialization) asserting every longest localized chain has both contracted endpoints. A second phrasing was searched. Existing upstream searches were retained and new searches were appended exactly from the command's log. There are no new-node statement/duplicate/source obligations, no long step over 2000 characters, no hidden non-elementary subclaim, and no SGA source. Every used node has a verbatim citation entry. Nothing was compiled or written to the shared repository or launcher.

## Repair of the returned delivery

The return at 2026-10-22 09:08 UTC names head `30aa55e723a`: the reader approved the mathematics, but the landing found a side completion that had not been promoted to the live DAG. I continued the retained delivered sandbox rather than recreating its proof or searches. Compared with the current read clone, the item has the identical statement, statement dependencies, source, chapter, unit, created record and blueprint ancestry; the current node is unsplit with empty proof fields. The retained differences supply the four-step split and the already logged Mathlib searches. The required initial deliver.py dry run rebased this retained work through its temporary worktree and passed preflight at `d1379fd4a8f`.

I re-opened all three current dependency records: `def-weil-pbc-localization-at-prime`, `def-weil-pbc-krull-dimension-ring`, and `lem-weil-pbc-primes-of-localization`. For the actual content used by the proof, all four retained citation quotes are still verbatim substrings of the current statements, and both proof dependencies are Mathlib leaves. Thus no changed dependency forces a different argument or extra hypothesis. In particular, clause (1) still explicitly gives contraction as an inclusion-preserving bijection onto the primes below the chosen prime, not merely a map of spectra.

To make the repair reviewable beyond a re-push, I expanded step 2: it now explicitly substitutes R=A and the prime m, identifies the contracted ideals with the stated inverse images, and shows that equality of adjacent contractions would contradict injectivity and the original strict chain. I also replaced the repeated omnibus source place on each step with the precise Tag 00KE or 00E3 argument it uses. The item's statement and route are unchanged. The report and split summary now identify the return and this comparison. I rechecked the field and dimension-zero singleton-chain cases, the integer ring at a prime, the nonzero-domain use in step 3, and the finite upper bound in both endpoint contradictions. No step exceeds 2000 characters, and every non-elementary input remains covered by its cited statement. The citations and logged searches are retained; no new search question or new node was introduced.

## Resumed repair comparison (2026-10-22)

The current return entry in `coord/returns/Q113.md` is dated 2026-10-22 12:45 UTC and names returned head `2cdf94fce04`. It again approves the reading but refuses landing because the side completion was not promoted to the live DAG, and asks for a rebase, rereading of changed citations, and adjustment before pushing. The retained dry-run receipt names `94a43148e6d`; the historical report above preserves the earlier returned head `30aa55e723a` and the repair already made from it. I resumed that sandbox, with its proof, citations and searches intact. The newly completed initial dry run rebased these files in the delivery tool's temporary worktree and passed at `d6575529a68`. Direct JSON comparison with the current read clone shows differences only in the split-owned fields: proof, proof dependencies, proof origin, status, split report and the additional logged searches. The statement, statement dependencies, source, created record, chapter, unit and blueprint ancestry agree exactly.

I reread all three current statement dependencies and proof dependencies, including the localization definition. The dimension definition still supplies both the supremum and the empty-spectrum convention, and clause (1) of the prime-correspondence lemma still supplies the inclusion-preserving bijection and inverse extension. All four citation quotes remain verbatim; there is no changed cited statement requiring a new hypothesis or a replacement lemma. I reread Stacks algebra.tex at `lemma-spec-localization` (Tag 00E3) and `definition-Krull` (Tag 00KE), morphisms.tex at `lemma-alteration-dimension` (Tag 02JX), and the current blueprint normal-cone proof of `lem-trf-local-term-locality`. The ancestry and route remain the same.

This continuation further clarifies step 1: the dimension hypothesis bounds every chain length in each ring, the positive finite supremum is attained by integer discreteness, and the zero case uses exactly the empty-spectrum convention. Step 3 now explicitly derives the strict first inclusion from containment of the zero ideal and inequality of the ideals. The arguments of the approved split are preserved. Steps 2 and 4 still use the prime correspondence and the append-a-prime contradiction respectively. The only substantial algebra input is the existing Mathlib prime-correspondence node; the remaining arguments are elementary and written out. I checked the singleton-chain case for fields, the length-one chain in the integers localized at a prime, and why the domain hypothesis is essential to prepend zero. The finite-type-over-a-field Lean declaration read on resumption has stronger hypotheses and is not an attachment for the item. No new nodes or search questions were introduced; the previous logged results were reused, with unavailable services still recorded as unavailable. No step exceeds 2000 characters.

## Unfinished work

None in the stage-1 split. Formal Lean proof is outside this dispatch's scope.
