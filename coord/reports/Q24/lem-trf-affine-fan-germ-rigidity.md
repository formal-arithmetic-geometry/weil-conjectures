# Stage-1 delivery: lem-trf-affine-fan-germ-rigidity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-fan-germ-rigidity.json`: statement item, split in three steps; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `searches.jsonl`: actual new searches made through msearch.py; inherited item searches retained in the node.
- `report.md`: this report.

Zero new nodes; zero Mathlib leaves. Only the sandbox was written. No Lean files, git commands, compilation, or build tools were used.

## Attachments

None. Searches of live `lean/WeilConjectures/` for the exact blueprint id, monoidal spaces, Kato fans and affine fans returned no project declaration stating this item. The supplementary `lean/Sheaf/` search located AffineFanHomUniversal.lean; its `affine_hom_universal` is a different, global universal property, with proof `sorry`, so it is not an attachment.

## WANTED

None. The ILO PDF is available and was read.

## Corrections and route

The statement is unchanged and is true under precisely the given hypotheses. Its original empty proof is replaced by the finite-generator shrinking argument and the existing canonical-section rigidity theorem. A generic etale stalk-spreading node would add scheme and etale-site hypotheses not available here; it is not used. No new lemma restates a clause of the item.

Read the chapter and unit records and their latest blueprint counterparts. The current blueprint ancestor `lem-trf-local-term-locality` has a contracting-correspondence proof and no fan assertion; this node explicitly records historical nearby-duality/alteration ancestry. Retained that ancestry and the original source intent, without changing unit or chapter data. Whole-blueprint searches `affine fan` and `germ rigidity` each returned zero imported equivalents. The existing DAG has the stronger global equality result `lem-trf-affine-fan-canonical-section-rigidity`, which supplies the only non-elementary input. It belongs to the same unit, so no off-unit tool use is needed.

## Mathlib searches

Ran msearch.py with leanfinder twice (different phrasings), loogle, grep and leansearch; all services answered in this run. Exact tool/query text and response summaries are in searches.jsonl and the item's mathlib_searches. Read the returned types: the algebraic geometry results are about schemes or ringed spaces, and the sheaf results concern germs and individual sections. In particular `germ_eq` is an elementary germ-equivalence ingredient already explicitly defined in `def-trf-fine-fan-blowup`; it does not prove morphism rigidity for monoid spectra. The scheme spreading-out results need `IsGermInjectiveAt` and ring-valued schemes. Neither phrasing found this item as an exact match or a one-line specialization.

## Not duplicates

No new nodes were created. The global canonical-section rigidity node is reused rather than duplicated. The local germ statement adds the finite-generation neighborhood argument to that existing global theorem.

## Review by Q24

I read ILO Expose VIII 3.1.3--3.1.8, printed pp.98--99, and the proof of Theorem 3.3.15, printed pp.109--110, directly in the PDF text. The proof there shrinks by fineness, then applies Lemma 3.1.8(ii). I opened the full statements of `def-trf-fine-fan-blowup`, `lem-trf-affine-fan-canonical-section-rigidity`, `lem-trf-affine-fan-hom-universal`, `lem-trf-affine-fan-localization-sections`, and `lem-trf-finite-monoid-stalk-data-spreading` before deciding which inputs to cite. There are no new-node sources to review.

Step 1 uses the definition node's explicit fineness (finite generation) and explicit stalk equivalence relation. Equality of each generator's two germs gives one neighborhood on which those two sections agree; the finite intersection remains an open neighborhood inside V. This needs neither finite presentation nor any condition on the section monoids beyond their stated monoid structure. I wrote this elementary argument in the item instead of creating another stalk-spreading node. The citation excerpt copies the actual equivalence-relation sentence, and the same definition's opening paragraph supplies finite generation.

Step 2 uses no theorem: preservation of zero and addition extends equality on generators to equality on every finite sum. I spelled out both the empty-sum base and adjoining-one-generator step, so no free-monoid presentation or uniqueness of expressions is assumed. Relations in P cannot affect the argument, since the given maps are already homomorphisms.

Step 3 cites the definition node for the unchanged stalks under open restriction, with the representative-neighborhood intersection argument explicitly given. Its non-elementary input is exactly the last assertion of `lem-trf-affine-fan-canonical-section-rigidity`, whose full statement I read. That assertion states equality of the entire local morphisms from equality of canonical-section maps, explicitly including point and sheaf maps. Its hypotheses hold for the restricted space: P stays fine and sharp, restricted stalks stay sharp, and stalk maps remain local. Restriction compatibility identifies the canonical-section pullbacks with the maps proved equal in Step 2. Thus no unproved point-map recovery or basic-open sheaf comparison is hidden in this step. citations.json contains the precise verbatim concluding sentence from the node, not its proof.

I tested P={0}: both section homomorphisms are forced and U=V works, using no generators. For P=N the single generator gives the required neighborhood, and for P=N^2 the intersection of two neighborhoods suffices. T need not be a scheme, separated, Noetherian, finite, or nonempty beyond t in V; none of those hypotheses enters. The source sheaf need not have finitely generated stalks, and P need not be saturated or torsion free. Restriction to U preserves every hypothesis used in the final theorem. Each of the three steps is below 2000 characters; no long argument conceals a new lemma.

Against delivery-errors B--E: there are no new-node format, definition, tag or duplicate obligations; all used objects and morphisms remain the original ones. Every non-elementary fact is the statement of the cited rigidity node; the other two steps write out only finite intersections, the explicitly defined germ relation, and monoid sums. The rigidity node has no dependency on this item, so the reused edge does not make a cycle. The proof keeps the source's shrinking-and-rigidity route rather than moving the conclusion into a new node. No source or statement error was found, and no hypothesis was silently added.

## Unfinished

Nothing in the requested one-level split. The existing rigidity dependency remains a separate stage-1 item; it is cited by statement, as required. Delivery validation and push results are supplied by deliver.py.
