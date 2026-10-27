## Worker report

Item: lem-sfb-normal-generic-component-comparison. Group Q12. Stage 1 only, 2026-10-22.

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-generic-component-comparison.json`: statement retained verbatim; six proof steps; status split; recorded searches and blueprint place; added the existing generic-point, function-field and affine-morphism definition dependencies.
- `citations.json`: six step/node entries with verbatim excerpts of the cited statements.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing affine permanence, affine qcqs and qcqs spectral statements are Mathlib leaves and are reused. The existing spectral clopen criterion is also reused.

Attachments: none. A search of `lean/WeilConjectures/` for the blueprint tag and for generic/component and clopen/basis language found no declaration giving every clause of this item. Related normal-constant-generic and spectral topology declarations do not state the local-basis gluing assertion and are not attachments. No Lean file was written and no compiler or Lake tool was run.

WANTED: none. The clopen gluing argument is an agent-written elementary argument, rather than a theorem claimed to occur verbatim in a missing source.

The sandbox initially contained no item, split, report or search log. The current repository item was used as the starting copy. Its statement is correct; no STATEMENT-DISPUTED correction is needed. Its source already distinguishes the spectral component criterion from Tag 0906 itself, and that distinction is preserved. The open obligations were the complete overlap argument and the affine/spectral preparation, not a change of hypotheses.

Nothing mathematical remains unfinished in this one-level split. The six steps total 2444 characters; none exceeds 2000 characters or hides a separately hypothesized comparison lemma.

## Sources and route

I read the chapter record `sec-six-functors-basics`, the assigned unit `sk-thm-sf-ctf-stability`, and the current `main-20261015` proof `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). This item is an auxiliary part of the normal generic continuous-section argument serving direct image preservation. That blueprint paragraph does not itself assert this generic-fibre topological lemma. Accordingly the proof origin is agent, and the source places identify the elementary expansion and the Stacks tools separately. The unit and chapter records were not modified.

`tools/blueprint_refs.py ancestor lem-sfb-normal-generic-component-comparison` reports a null blueprint ancestor; I retained the inherited `from.node = null`, its detailed place and its via list. Searches of the whole blueprint for `generic component` (zero results) and `clopen` (12 results) do not provide this statement. The latter results concern supported cup products, proper/open comparisons, Stonean covers, w-contractible partitions, clopen sections, w-local partitions and local terms. The item therefore has `same_as = []`. No new node requires a blueprint backlink.

The source tools read were Stacks `morphisms.tex`, Tag 01S6 (`definition-affine`) and Tag 01SD (`lemma-base-change-affine`); `algebra.tex`, Tag 00E8 (`lemma-quasi-compact`); `schemes.tex`, Tag 01KN (`lemma-affine-separated`); `properties.tex`, Tag 094L (`lemma-quasi-compact-quasi-separated-spectral`); and `topology.tex`, Tag 0906 (`lemma-spectral-pi0`). I checked the tag-to-label map as well. Tag 0906 proves profiniteness of component quotients, not the homeomorphism criterion: the last step cites the existing node that states the criterion in full.

## Mathlib searches

All searches used the required `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q12 lem-sfb-normal-generic-component-comparison` command. The exact queries and actual returned names are in the item's `mathlib_searches` and the command-generated `searches.jsonl`. Both LeanFinder phrasings, Loogle, grep and LeanSearch returned successfully; no service was unavailable.

The first LeanFinder phrasing returned fibre homeomorphisms and gluing of topological open covers; the second returned integral and affine scheme properties. Loogle returned `ConnectedComponents.equivOfIsClopen` and its connected-piece variants: their hypotheses are a disjoint clopen decomposition, rather than inverse-image bijections on a basis. LeanSearch returned quotient-map clopen reflection, ordinary equivalence/homeomorphism constructors, idempotents of spectra and open-immersion restriction. None supplies the full item or a one-line specialization of it. The targeted generic/functionField versus ConnectedComponents/IsClopen grep returned zero hits. These are absence conclusions for the full item, not claims that the separate affine or spectral tools are absent.

## Not duplicates

No new nodes. I searched the whole DAG for spectral clopen/component comparison, affine base-change permanence, affine qcqs, qcqs spectrality and generic/basis clopens. This found the exact existing tools used below, so no copy of any of them was created. In particular the spectral clopen criterion is `lem-sfb-spectral-clopen-component-homeomorphism`, not a newly relabelled clause of the item.

## Review by Q12

I checked the item and every cited statement with their files open against delivery-errors B–E. The statement introduces the integral base, its function field and generic inclusion, the arbitrary affine source, its generic fibre, the basis and all local inverse-image hypotheses. The integral and affine notions already have definition nodes; the additional statement dependencies identify the existing generic-point, function-field (including its general integral-scheme clause) and affine-morphism notions. Clopens, connected components and the quotient topology are explicitly defined in the statement. No normality, Noetherian hypothesis, finite presentation or quasi-separatedness of the base is inserted.

Step 1 uses `def-weil-affine-spectrum` exactly for its sentence that the spectrum of a field has one point. The inverse image of an open under the given map from that one-point scheme is the whole scheme or the empty scheme, both affine. The empty scheme is the spectrum of the zero ring, since that ring has no prime ideals. `pqf-def-affine-morphism` says precisely that testing preimages of every affine open proves affineness. This is elementary and does not require an assertion that intersections in X are affine. The argument actually works for any morphism from the spectrum of a field; the generic inclusion is its instance.

Step 2 uses clause (1) of `lem-weil-pbc-affine-morphism-permanence` for the actual pullback of j along u, and clause (2) for the affine target U. Those statements impose no quasi-separatedness hypothesis on X. `lem-weil-pbc-affine-scheme-qcqs` gives both required properties of each affine scheme, including the empty one. `lem-weil-pbc-qcqs-scheme-spectral` has exactly those hypotheses and gives spectrality. The full statements of these three nodes are quoted in citations.json so that both clauses of permanence are visible. These are existing Mathlib leaves, so using them across units is an allowed tool use without changing the unit route.

Step 3 uses the local bijection in the item's hypothesis, not an unquoted result about normal schemes. Existence chooses C_W for the restriction of D. For B in the basis contained in an overlap W intersect V, the restrictions of C_W and C_V are clopen in B and have the same inverse image. The assumed injectivity for B proves equality there. The basis condition supplies such B about every point of the overlap, proving equality on the whole overlap. The intersection itself is never treated as affine. These are restrictions, equality of inverse images, and pointwise equality of sets, so the step is elementary and needs no additional lemma node.

Step 4 explicitly forms C as the union of the C_W, proves its restriction to each W, and writes its complement as the union of the W minus C_W. Relative openness of both pieces inside the open W proves that both global unions are open. The inverse-image calculation gives D because the inverse images of the basis cover U_eta. Thus surjectivity is proved in the item's own steps, without exporting a clause to a new node. No compactness, finite subcover, surjectivity of i or general descent theorem is used.

Step 5 proves injectivity by restricting two clopens to every basis member and then taking unions. Continuity of the underlying map of a scheme morphism ensures its inverse image preserves open and closed subsets. This is elementary topology and uses only the stated local injectivity, not the conclusion of another unproved lemma.

Step 6 uses the exact statement of `lem-sfb-spectral-clopen-component-homeomorphism`: continuous f between spectral spaces, bijective inverse image on clopens, the induced component homeomorphism and its normalization. Step 2 supplies its two spectral hypotheses and steps 3–5 supply its bijection hypothesis. Its statement expressly permits empty spaces. I read this node's statement, rather than taking a homeomorphism assertion from the proof of the weaker Tag 0906. This node has the same unit as the item. No off-route unsplit theorem or new tool-use declaration is needed.

Small cases checked: U empty, including an empty basis; redundant or infinite bases; empty basis members; empty and full D; and a nonempty basis member with empty generic fibre. In the last case the local bijection hypothesis is impossible, since the distinct clopens empty and W would have the same inverse image; the proof does not silently assume the fibre projection surjective. For empty U all unions and quotient spaces are empty and the clopen sets on both sides form a singleton. The proof also works over non-quasi-separated X because affineness of j is tested one affine open at a time and the overlap gluing uses basis refinement only.

Corrections during this reading: the unsplit item's missing proof has been filled; the generic inclusion is handled directly instead of by an unnecessary localization comparison; the final component conclusion is taken from the existing full criterion, not directly from Tag 0906. No statement weakening, hollow definition, SGA source, new lemma or new Mathlib leaf was introduced.

The server-only preliminary checks both exited successfully: `check_dag` introduced no findings and `review_split` reported PASS with zero new nodes. Its note that the unit has no realization recorded is inherited; this auxiliary item is not the unit key statement and does not edit that record.
