# Stage-1 report: lem-trf-countable-flat-ml-sequential-presentation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-countable-flat-ml-sequential-presentation.json: statement, split; no Mathlib match, statement unchanged.
- citations.json: six verbatim statement quotations covering every proof-step citation.
- searches.jsonl: actual msearch.py results, retained without alteration.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The item is split using existing nodes.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id, countable flat/free/presentation terms, and Mittag-Leffler terminology. The project hits concern towers of groups/sheaves, K-flat complexes, and ideal-power limits, not this tensor-Mittag-Leffler module statement. The existing Sheaf Lazard presentation is a dependency already carried by lem-kun-lazard-flat-module, not an exact attachment of this item.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/algebra.tex.

## What was wrong or missing

The imported item had no proof. Its statement is correct and its statement dependencies are retained. The distinction between an arbitrary directed finite-free presentation and a countable one matters: I use the actual statement of lem-trf-ml-countable-colimit to obtain the latter, rather than inferring countability from generation alone. Finite free stages are finitely presented because the zero map from rank zero presents them; no finiteness of their transition kernels is presumed.

The inherited blueprint.from.place describes a historical semistable-alteration input using Tags 05FT and 05FQ. I read the latest blueprint at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md and the latest unit/chapter, together with the DAG ancestor's current proof and blueprint_update. The current ancestor proof uses contracting correspondences and deformation to the normal cone and no longer says the historical 05FT clause. I retain the already assigned ancestry and explicitly record this discrepancy in split_report.blueprint. This delivery proves the same local algebra item below its recorded route; it does not alter any unit, chapter, target, ancestor or provenance chain. The current source for the local algebra assertion is precisely Stacks 059X/059W.

The source paragraph after 059W says that a countable directed set has a cofinal subset isomorphic to the natural numbers. Literally that formulation overlooks a finite directed set. The needed and valid statement is a cofinal nondecreasing sequence, allowing repetitions. The proof uses this version. The item already allows repeated modules and arbitrary transition maps, so no statement correction is necessary.

## Unfinished work

None in this one-level split. Existing dependency nodes keep their own statuses; this delivery does not re-split or edit them.

## Not duplicates

No new nodes were created. Searches of the whole DAG by 059W, 059X, 058G, Lazard and cofinal/countable terms found the existing countable-extraction and Lazard nodes, which are reused. Whole-blueprint searches with blueprint_refs.py for Mittag, countable, Lazard and sequential finite found no exact blueprint counterpart for this item. The general Mittag-Leffler tower blueprint result is about finite groups and is not this tensor condition.

## Mathlib searches

Seven searches ran through msearch.py and their actual records were appended to the item's prior searches. LeanSearch was available this time: the hits concern finite presentation and finite flat projectivity, requiring finite generation/presentation beyond this item's countability. LeanFinder returned finite-relation flatness criteria and general direct-limit tools, then general direct-limit representatives and finitely generated submodule presentations on the second phrasing. Loogle returned no hits for either Module.Flat with IsColimit or Module.DirectLimit with Module.Free. Grep found only an adic-completion comment for the first pattern and no matches for the second. These do not directly state, or specialize in one line to, the item's sequential finite-free presentation. Existing logged searches in the item were retained, including the earlier unavailable service result.

## Review by NQ

I read the actual local Stacks source: 059X (lemma-countgen-projective), opening two sentences; 059W (lemma-ML-countable-colimit), including its entire proof and the following sequential-indexing paragraph; 0597 (lemma-ML-limit-nonempty), whose proof constructs successive upper bounds; 058G (theorem-lazard); 00HD (lemma-flat) and 00HB (definition-flat); and 00DF (lemma-tensor-product-exact). No new node needs a separate source review.

For Step 1 I opened all three cited nodes. lem-weil-pbc-flat-tensor-exact states preservation of exact sequences and the initial zero term for a flat module; it does not explicitly state terminal surjectivity, so I separately cited lem-weil-pbc-tensor-right-exact, which does state it. Together these give exactly the short-exact-sequence preservation assumed by lem-kun-lazard-flat-module. That node's statement explicitly supplies a small nonempty directed poset, finite coordinate-free ranks, compatible maps, and the colimit isomorphism. The base is the same commutative ring R, and P is the same module throughout. This avoids taking the Stacks hypothesis merely from its definition or borrowing an unstated consequence from the proof of Lazard.

For Step 2 I read the complete statement of lem-trf-ml-countable-colimit. It permits a small nonempty directed poset with finitely presented stages and requires tensor-Mittag-Leffler and at most countable generation of the colimit. All are present. The finite-presentation check is written as the cokernel of R^0 to R^r, matching that node's inline definition rather than a different categorical finite-presentation notion. The existing definition def-trf-mittag-leffler-module is exactly the tensor-to-product injectivity notion used by both item and extraction node. The second citation, def-weil-pbc-category-colimit, gives the actual universal property and canonical map, so an isomorphism of cocone vertices transfers that property. No cofinality of J in I is asserted: only the extraction node's canonical colimit isomorphism is used.

Step 3 is elementary recursion: enumerate the nonempty countable J with repetition, choose a pairwise upper bound at each successor, and check the two induction inequalities. This is the full argument, not a hidden general cofinality lemma. The stages need not be submodules of P. In particular no transition is assumed injective, and the ranks can be zero. A finite J, even a singleton, is handled by padding the enumeration, not by claiming a strictly increasing infinite subset.

For Step 4 the sole cited definition is the universal property of colimits. I checked every formula: h_i uses a transition inside the same J diagram; two choices are compared at an index l at least their two sequence positions; compatibility for i at most k is obtained at a sequence term above k; the extension restricts back to the original h_n; and uniqueness of a sequential factorization follows from uniqueness over J. This explicitly proves cofinal reindexing rather than citing an unrelated filtered-colimit existence node or silently using a cofinality theorem. All index categories remain small. Both elementary steps are under 1000 characters and contain no non-elementary borrowed assertion.

I checked delivery-errors B through E against the actual files: no new statement-only payload can hide the proof or repeat the item; all six citations have literal statement quotations; proof_deps is their exact union; each source names the tag and TeX label; no Mathlib search was invented; no SGA source is used. The two substantial sources are existing smaller statements (general Lazard presentation and countable extraction), and the item's proof assembles them with the explicit sequence and cocone arguments. No dependency is the countable-flat-projective parent or otherwise relies on this item. I checked zero ring, zero module, empty generating subset, finite generation, finite/singleton extracted index set and vanishing ranks: nonemptiness comes from the cited presentation/extraction statements, so each construction still works. All steps are under the 2000-character review threshold.

The Lazard node is a generic tool from another unit, used exactly as in the opening of Stacks 059X; its explicit tool-use justification is recorded in split_report.tool_uses. The two tensor lemmas and colimit definition are Mathlib leaves. No unit route is replaced and no maintainer-owned tool_uses or review field is written.
