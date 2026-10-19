Files written:

- `dag/nodes/sec-six-functors/lem-coef-infinity-preserves-essential-small-colimit.json`: statement node, split into three proof steps; no new node and no Mathlib leaf.
- `citations.json`: verbatim quotes for both cited nodes in Steps 1 and 3.
- `report.md`: this report.

Attachments: none.

WANTED: Kerodon Proposition 7.2.2.9 (tag 02XT), including its equivalence-index specialization; the online source was read, but no archival copy is present in `literature/`.
WANTED: Kerodon Proposition 7.1.6.19 (tag 02X1), used for the terminal-base absolute-colimit identification; the existing DAG node records the same online source.

No statement error was found. The item is not already declared in either read-only Lean source checkout. I searched the whole DAG and blueprint for the statement and for equivalence-indexed colimit preservation; the existing nodes `lem-coef-infinity-absolute-terminal-relative-colimit` and `lem-coef-infinity-relative-cone-equivalence` provide the needed general facts, so no duplicate node was created.

## Review by Q17

I read the item node, the `sec-six-functors` chapter record, the `sk-prop-sf-biduality-general` unit record, the item’s Kerodon source location, and the complete statements of both cited nodes. Step 1 chooses an explicit equivalence from a genuinely `\\mathcal U`-small quasicategory and uses the absolute-terminal node to identify ordinary colimitingness with the relative predicate; the equivalence node’s clause (2) says exactly that the specified cocone remains a colimit after this reindexing. Step 2 uses only the item’s hypothesis that `H` preserves every `\\mathcal U`-small colimit, so it applies to the reindexed cocone and preserves its exact boundary, apex, and coherent simplices. Step 3 applies the same two statements to `Hq` and transports colimitingness back, proving the original specified image cocone rather than choosing another colimit. Every cited quote in `citations.json` is copied verbatim from its node statement, and `proof_deps` is the union of the non-elementary uses. I checked the empty-index case, an identity equivalence, a finite/small index, and a non-small index equivalent to a small one; all follow without extra hypotheses. The two Mathlib searches of each service plus grep were rerun for this item and recorded in `searches.jsonl`; they found only ordinary-category analogues, so the item remains non-Mathlib. No Lean was written or compiled, no live project file was changed, and no SGA source was used.

What could not be finished: none. The split and mathematical self-review are complete.


## Resumption check, 2026-10-17

I retained the earlier split, citations, report and search log. The statement and all pre-existing metadata fields still agree with the current repository; its item is unsplit. I read the existing search results rather than repeating their unchanged questions. The exact-tag and concept searches under `WeilConjectures/` found no project declaration for this coherent quasicategorical statement, including no attachment in the master reference checkout. I also read the ordinary-category candidates in `Mathlib/CategoryTheory/Limits/Preserves/Basic.lean` at lines 124 and 352–359 and `Limits/IsLimit.lean` at lines 400–403. Their functors and cocones are those of ordinary categories, so these hits do not make this item a Mathlib leaf.

For the source check I reopened [Kerodon 02XT](https://kerodon.net/tag/02XT), [02X1](https://kerodon.net/tag/02X1) and [02XQ](https://kerodon.net/tag/02XQ). Proposition 7.2.2.9 gives the existence comparison; its cited Corollary 7.2.2.2 gives the criterion for a particular cone. Their colimit dual at an indexing equivalence is precisely clause (2) of the existing relative-cone-equivalence node, which the proof uses. The absolute-terminal node explicitly identifies its relative predicate with initiality of the coherent cocone. Thus neither step 1 nor step 3 substitutes an existence-only assertion for the given cocone.

I checked the smallness hypothesis of the absolute-terminal node against both uses: its word “small” is instantiated in the sufficiently large containing universe already fixed in the item, so it covers both K and K_0. Only K_0 must be small in the original universe U in step 2. The terminal functors are inner fibrations by the cited node, as required by clause (2) of the equivalence node; their base diagrams are unique, so all compatibility hypotheses hold. Reindexing and postcomposition compose as simplicial maps, giving the exact equality (Hq)e^▷ = H(qe^▷), including higher simplices. No existence assumption for additional colimits is introduced.

The four citation quotes remain verbatim substrings of the current cited statements. The three proof steps have lengths 616, 328 and 491 characters; there is no step over 2000 characters or hidden extra lemma. No new node needs the B1–B9 or same-tag duplicate checks. The existing essentially-small-cocones node concerns size of a cocone category, rather than preservation of its initial object, so it supplies no attachment or substitute statement. The whole-blueprint searches for “colimit equivalence” and “essentially small” found no equivalent imported statement. I read the master and main-20261015 blueprint ancestor text; this is generic infrastructure below its existing derived-system realization route, with the inherited unit and ancestry unchanged. Both proof citations are in the item's unit. No target statement or coefficient category changes.

The first resumed dry run found only the report sentence “pending the delivery dry run”; I replaced it because the mathematical review is already complete. The proof, statement, citations and recorded searches required no repair.
