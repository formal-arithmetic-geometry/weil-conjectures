# Worker report: lem-sfb-closed-orbit-component-map

Group Q104; stage 1; direct delivery; 2026-10-23.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-orbit-component-map.json`: existing statement, now split into seven elementary steps; no Mathlib match for the whole item.
- `citations.json`: five verbatim statement quotations, one for each node citation in the seven steps.
- `report.md`: this report and signed review.

There are **0 new nodes and 0 new Mathlib leaves**. The statement, statement dependencies, source, creation record, chapter, unit and inherited blueprint provenance are unchanged. The item had no sandbox node or report when this attempt began. There is no released repair note for it. Existing 2026-10-22 Mathlib search records are retained, with the five actual searches of this attempt appended from `searches.jsonl`.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for closed-orbit/component-orbit and generic-point/stabilizer combinations found no declaration proving this item. The analogous keyword check of `lean/Sheaf/` also gives no such declaration. The parent's `finiteQuotient_genericFields` theorem is about normal Noetherian schemes and does not prove this arbitrary-space assertion; its sorry statement is not an attachment.

## Literature wanted

None. The entire argument is an elementary consequence of the definitions and the explicit hypotheses, rather than an invocation of an unavailable theorem.

## Issues found and repaired

The imported node had no proof. I supplied the seven arguments, including details that can otherwise be concealed in the phrases “a homeomorphism permutes components”, “the image is a component”, and “the generic stabilizers coincide”. No mathematical error or statement dispute was found. Sobriety is already defined inline by the item's hypothesis; no definition node is being cited for an existence/uniqueness theorem. The finite group action and orbit-fibre properties are hypotheses, so this split does not invoke the affine invariant-quotient theorem of Stacks 03BL.

The item inherits `blueprint.from.node = null`. `python3 tools/blueprint_refs.py ancestor lem-sfb-closed-orbit-component-map` explicitly returns `None`, so I retained that value and its via chain. I read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, refreshed to the snapshot recorded as main-20261023-1620 in COMMITS.txt. Its current direct-image paragraph (3) assembles compactification and open/proper direct images; the ancestor's older alteration wording survives only in the inherited provenance. This auxiliary topology still realizes the use in `lem-sfb-finite-quotient-generic-fields`, Step 3, along the already established chain. It changes neither a chapter nor a unit route. I also read the repository chapter and unit records; the historical unit record has chapter `sec-six-functors`, whereas the item and current latest blueprint use `sec-six-functors-basics`. That inherited indexing discrepancy is not changed in this delivery.

## Duplicate and blueprint searches

Before considering any new lemma, I searched all `dag/nodes/` for Tags 004V/004X and for continuous images, generic-point images, homeomorphism/component and component/orbit combinations. I ran `python3 tools/blueprint_refs.py search 'irreducible component'` (13 blueprint hits) and `search 'orbit'` (3 blueprint hits). The former concerns scheme affine neighborhoods, normal components and function fields; the latter concerns affine-line data, Frobenius conjugacy and Euler-product orbits. None states this topological closed orbit-map theorem. No nodes were created: the closed-cover, inverse-homeomorphism, set-saturation and closure calculations are included in the steps themselves. A source tag occurring in another node is not used as a reason to replace the explicit argument with an inapplicable scheme lemma.

## Mathlib search results

I ran the required `msearch.py Q104 lem-sfb-closed-orbit-component-map` commands for leanfinder, loogle, grep and leansearch, followed by a second semantic phrasing. The exact queries and actual results are in `searches.jsonl` and copied into `mathlib_searches`. All five services/calls returned successfully this attempt. Older retained LeanSearch unavailability remains recorded as unavailable.

I read `Topology/Irreducible.lean:463-520`: `image_mem_irreducibleComponents_of_isPreirreducible_fiber` and `irreducibleComponentsEquivOfIsPreirreducibleFiber` require open maps and preirreducible fibres. A two-point discrete space with the swapping action has a two-point fibre over its one-point quotient, so that fibre hypothesis fails here. The generic-point search hits in `Topology/Sober.lean` give the definition, generic-point/component correspondence, or irreducibility of a generic closure; none provides orbit saturation or component maximality for this map. I read the generic-image calculation at Sober.lean:98-100, which confirms the closure calculation but is proved explicitly here in a few lines. Quotient covering trivializations require disjoint translates and thus exclude the nonfree actions allowed by the item. `MulAction.selfEquivSigmaOrbits` and its variant give a set decomposition, not the topological component conclusions. `PreGaloisCategory.has_decomp_quotients` is about finite discrete continuous actions in Galois categories. These are not one-line specializations giving all item clauses.

## Not duplicates

No new nodes, hence no new/existing source-tag pairs require comparison. The two existing definition leaves are reused directly.

## Review by Q104

I read Stacks `topology.tex`, `definition-irreducible-components` (Tag 004V), `lemma-image-irreducible-space`, and `definition-generic-point` (Tag 004X, particularly parts (1) and (4)). I checked the application context in `groupoids.tex`, `lemma-points` (Tag 03BL); the orbit-fibre conclusion of that lemma is an assumption here, not an uncited input. I read both cited JSON statements in full. `def-weil-irreducible-components` really states nonempty irreducibility by relatively closed covers and component maximality; `def-sc-generic-point` really states closure of a singleton equals the specified subset. All five citation quotations are literal substrings of those statements. This is an agent-written elementary proof checked against those sources, and `proof_origin.by` correctly says `agent`.

Step 1 uses the definition of irreducibility and maximality, both in `def-weil-irreducible-components`. It applies the closed-cover definition under each homeomorphism and then under its inverse to prove maximality. No theorem saying homeomorphisms permute components is hidden or cited from a definition.

Step 2 uses only invariance, bijectivity of the action maps, and the assumed point-orbit description of fibres. For each orbit union it proves both equal-image and saturation by explicit element calculations. The orbit is nonempty because it is an orbit of an existing component; empty spaces are handled separately.

Step 3 uses finite component count, their assumed clopenness, closedness of q, saturation from Step 2 and surjectivity of q. I verified the complement identity rather than presuming an arbitrary continuous image of an open set is open. No quotient-map theorem is invoked.

Step 4 uses the irreducibility clause of `def-weil-irreducible-components` and writes out the two closed inverse images. Continuity is a stated assumption and q restricted to C is surjective onto q(C) by definition. Nonemptiness comes from the component definition. Thus the continuous-image lemma is proved within the step rather than introduced as a redundant new node.

Step 5 uses that same node's maximality clause. The image blocks are nonempty, disjoint, clopen and cover Z by Steps 2-4 and surjectivity. An irreducible subset meeting a block cannot meet its complement: those intersections are a relatively closed decomposition and the complement piece cannot be the whole set because the first piece is nonempty. This proves both maximality of each block and exhaustion of the existing components, with no unstated component-existence or finite-union irreducibility lemma. Distinct orbits give distinct images. I checked the statement's “exactly one component” and “bijection” clauses individually.

Step 6 uses exactly the closure equality in `def-sc-generic-point`. Existence of eta_C is from the explicit sobriety assumption on X, since C is a nonempty closed irreducible subset. Closedness of q(C) gives one closure inclusion. For the other, a closed subset of Z containing q(eta_C) pulls back to a closed set containing eta_C and therefore all of C. The two inclusions establish the generic-image clause without an implicit density theorem. Sobriety of Z makes this its unique generic point, as required by the phrase “the generic point”.

Step 7 uses the same generic-point definition and proves the closure equality under h by two inclusions, then uses the uniqueness part of the stated sobriety hypothesis on X. Both directions of the stabilizer equality are present; no faithfulness or freeness is assumed. The homeomorphism image hC is a component by Step 1. Finally, a surjection from the empty space has empty codomain, so the empty component-orbit bijection is valid.

I tested the statement on: X=Z=empty; the trivial group and an identity map on an irreducible space; an action swapping two discrete components with one-point quotient; a trivial action by a nontrivial finite group; and a nonfaithful permutation action with a nontrivial kernel. The swap case specifically prevents use of Mathlib's preirreducible-fibre component theorem. The proof never divides by the order of H or assumes generic freeness. The finite-component hypothesis is used only for closedness of the orbit union; the target's stronger finite/clopen assumptions are retained exactly.

Against delivery-errors B-E: no new statements or notions are introduced, the item statement is unchanged, TeX is escaped once, Stacks places name tags and labels, and the searches are actual logged calls. C1/C4 are met because every nontrivial-looking topological transport is written as a short direct argument; the two citations give precisely the definitions used, not external theorem content. There is no relabelled clause moved to a new node and no cycle: the only proof dependencies are existing definition leaves. Every step is shorter than 2000 characters (429, 347, 362, 391, 673, 462, 632 respectively); none hides a standard comparison or an independent auxiliary hypothesis. I corrected no statement, and left no mathematical gap or unfinished task.

## Validation and delivery

The required `deliver.py Q104 lem-sfb-closed-orbit-component-map --no-push` exited 0 with `OK (not pushed)` at 675ad5c0afe and reported that server preflight passed, including the server-side DAG and split checks. The report then corrected its citation count from six to five, matching the actual five verified entries; a final dry run is required for this report revision before pushing. No Lean was written or compiled. No repository or launcher file was modified.
