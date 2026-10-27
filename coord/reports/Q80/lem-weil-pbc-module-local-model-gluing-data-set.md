# Q80: lem-weil-pbc-module-local-model-gluing-data-set

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-local-model-gluing-data-set.json`: statement, split into four proof steps; not a Mathlib leaf.
- `citations.json`: exact statement excerpts for the two node citations.
- `report.md`: this report. Search commands also produced `searches.jsonl` in this sandbox.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this created supporting item is not the key statement of its unit.

## Attachments

None. Searched project Lean under `lean/WeilConjectures/` for the exact item id and for module gluing, gluing-data sets, and prescribed local families. The project theorem `AlgebraicGeometry.glue_sheaves_of_modules` in `Topology/GlueSheavesOfModules.lean` gives effectivity for one datum, but does not assert the set-sized parametrization over all covers and labels. Its object-gluing component is `AlgebraicGeometry.module_object_open_descent` in `Topology/ModuleObjectOpenDescent.lean`. Neither alone states the item. The scheme-module descent files also concern effectivity rather than this set of all tuples. No partial statement is offered as an attachment.

## WANTED

None. All sources used are present locally.

## Source and statement audit

Read Stacks `modules.tex`, Tag 01BC, `lemma-set-isomorphism-classes-finite-type-modules`, lines 957–984. Its proof explicitly parametrizes by local quotient modules and transition maps, observes that gluing data form a set, restricts covers to ones without repetitions, and then forms a set of glued modules. Our local modules are already prescribed, so its set-size argument applies without the quotient-module construction. Read `sheaves.tex`, Tags 00AL (`lemma-glue-sheaves`, first proof) and 00AM (`lemma-glue-sheaves-structures`), including the compatible-sections formula, the comparison isomorphisms, and the equalizer argument for module structures. These are exactly the sources of the existing module-gluing input.

The item's statement is correct and is preserved verbatim. It has no finite-presentation or finite-type hypothesis and needs none. Its cover is a subset of the opens, exactly the no-repetition convention in 01BC. Including diagonal transition maps and all triples is essential: the cocycle with all three indices equal gives phi_UU = phi_UU squared, hence phi_UU = identity by invertibility. The source does not require a separate diagonal axiom.

Read the current main-20261015 proof of `lemma-weil-pbc-h1-constructible-representation` in `sk-lem-pbc-p1-injective-fibre`: paragraph 2 invokes the finite-pushforward lemma. The item's inherited ancestor/via chain supplies the small indexing input below that lemma; no change of unit route is proposed. Searches with `tools/blueprint_refs.py` for `gluing modules`, `gluing`, `glueing`, `01BC`, `local module`, and `set of all`, together with whole-DAG searches by tag and module/sheaf gluing statements, found no blueprint node stating this parametrization. The existing gluing theorem is reused instead of being restated as a new lemma.

## Review by Q80

I checked B–E of `coord/delivery-errors.md` against the node files and the above sources. There are no new statement-only nodes, renamed clauses, or duplicate nodes. The proof retains the actual set-size argument in the item; no assertion is moved to a new input. After the repair, its four steps have 653, 608, 618, 773 characters; no step exceeds the long-step review threshold.

Step 1 uses the statement of `def-weil-sheaf-of-modules-category`, opened at `dag/nodes/sec-smooth-purity/`. It explicitly defines a module morphism to be a sheaf morphism whose every component is linear. A morphism is therefore encoded by one function on sections for each open. The product of those function sets is small; naturality and linearity are predicates, and inverse pairs are another subset of a product. This proves local Hom and Iso smallness from the definition, without assuming a separate essential-smallness theorem for the category of sheaves. The quotation in `citations.json` is the literal sentence defining morphisms.

Step 2 uses Step 1 and elementary closure of a Grothendieck universe under powersets, dependent sums/products and subsets. Its displayed ambient set includes all subsets of the opens, all label choices, and every ordered-pair isomorphism. Filtering by covering and cocycle conditions gives precisely D; no morphisms or covers are silently discarded. This elementary encoding is written out rather than made into a new lemma.

Step 3 uses clause (2), not the proof, of `lem-weil-pbc-glue-sheaves-of-modules`, whose entire statement I read. It states existence of a module sheaf, local isomorphisms directed from the global restriction to each local object, and exactly the equation phi_UV composed with theta_U = theta_V. Its cover, ringed-space, equal-index, and triple-cocycle hypotheses are provided verbatim by the item. In particular, it assumes neither quasi-compactness nor separatedness nor finite type, and its composition order agrees with ours. The citation quote is a literal substring covering clause (2). This is an existing same-unit input, so no off-unit tool declaration is needed.

Step 4 chooses the entire witness (module and all comparison maps) over the set D. The repair spells out the ambient witness set: section assignments are functions from Op(X) to the fixed universe, which is a set in a larger ambient universe; module operations, restrictions, and comparison maps are encoded by function sets, and their axioms cut out subsets. Ordinary set-indexed choice applies to those nonempty witness sets; its outputs still have the original section universes. This avoids confusing a set of indices with a small object type or requiring choice on arbitrary classes. Only existence of this family is claimed, not canonical dependence or uniqueness. The cited gluing theorem is not used for a construction its statement does not expose. No new data definition is made from an unproved existence theorem.

Checked edge cases explicitly. If X is empty, the empty cover is permitted: all the products over it have their unique empty tuple, and module gluing supplies the unique trivial sheaf on the empty space. If an I_U is empty, covers using that open contribute no label choices; D may be empty and then the conclusion is the empty family. Infinite covers are allowed because the universe is closed under small products and the gluing theorem has an arbitrary index set. Empty intersections cause no difficulty, since their module sheaves have the unique section required by the sheaf axiom. No nonempty cover or nonempty D is assumed. No source error or correction was necessary.

## Mathlib searches

Preserved all inherited search records, including Q54's unavailable LeanSearch result. Ran six fresh searches through the required `msearch.py` command; their exact tools, queries and results are recorded in the item and `searches.jsonl`. LeanSearch and both LeanFinder phrasings returned local-generator/presentation structures, abstract or spatial gluing data, or smallness of the sections of a limit. Loogle `SheafOfModules, "glue"` returned no hits. Both required grep searches were run through `msearch.py`.

Read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`, lines 425–440: `QuasicoherentData.bind` assembles local presentation data for a global module already given, and does not construct or parametrize all glued modules. Read `Sheaf/Limits.lean`, lines 26–60: its smallness concerns sections of a fixed diagram and its sheaf assertion concerns a limit cone. These do not specialize in one line to the item. The abstract descent and space-gluing hits likewise do not assert a small collection of our prescribed-module cocycles and simultaneous effective realizations. Thus no Mathlib match was claimed.

## Not duplicates

No new nodes were created; there are no new/existing node pairs to justify. Existing module-gluing and compatible-family nodes were inspected. They supply effectivity or explicit compatible-sections objects for one datum, whereas the present item supplies the set of all covers, local labels and cocycles and a D-indexed family. The parent finite-presentation representative theorem uses this family and is not used as a dependency, avoiding a cycle.

## What was wrong or unfinished

The item had no proof; no statement defect was found. All inherited metadata, sources, citations, and search history are retained. No mathematical part remains unfinished. Delivery validation is recorded below after the required dry run.

## Validation

The required `deliver.py Q80 lem-weil-pbc-module-local-model-gluing-data-set --no-push` exited 0 and printed `OK (not pushed)` at `889244eff95`: server preflight passed, including the DAG and split checks. No compiler, Lake, or local preflight/checker was run. The push invocation follows this successful completed dry run.

## Repair of return L (2026-10-22)

The returned branch head is `58ee681a967`. L approved the mathematical reading but refused landing because the completed side-project node had not been promoted to the live DAG. I retained the delivered four-step proof, sources, citations and all logged searches, and compared this retained delivery with the current repository item. The current live item is still `unsplit` with empty proof; its statement, statement dependency, source and blueprint ancestor/via chain agree with the retained version. I reconstructed the sandbox item from that current record, carrying over the reviewed proof and search history rather than treating the earlier side completion as live completion. The required delivery tool builds on the current server DAG; promotion and landing remain L's operation.

I re-read the full current statements of both proof inputs: `def-weil-sheaf-of-modules-category` still defines the sectionwise linear morphisms used in Step 1, and clause (2) of `lem-weil-pbc-glue-sheaves-of-modules` still provides exactly the arbitrary-cover, all-pairs cocycle gluing and local identifications used in Step 3. Both retained literal quotes pass substring checks against these current statements. No changed hypothesis or composition direction requires a different citation. I also re-read Stacks 01BC and 00AL/00AM and the current ancestor's finite-pushforward paragraph.

This repair changes Step 4 substantively: it explicitly constructs the ambient set of possible module-sheaf structures and comparison maps before applying choice, instead of just asserting that witnesses can be viewed in an ambient universe. This is a set encoding using function sets and subsets, and needs no new lemma. The statement, unit route, two dependencies and empty/infinite-cover cases remain valid. No search question or statement changed, so the previous search results were read and retained without redundant queries. No new nodes or Mathlib leaves are added.

The interrupted-turn check found no active delivery process. The first required repair dry run exited 0 and printed `OK (not pushed)` at `585b233ec27`. A final dry run of the edited repair and the push are still required.


## Resumed repair of latest return L: 0efb9cddd11

The current `coord/returns/Q80.md` entry is dated 2026-10-22 09:12 UTC and names returned head `0efb9cddd11`; the `58ee681a967` discussion above is retained history of the preceding attempt. The required first dry run on the retained sandbox completed with exit code 0 and `OK (not pushed)` at `6f14806e37c`. No interrupted transport or missing final answer was treated as invalidating the retained proof.

I compared every field of the sandbox item with the current shared DAG item: the only differences before this resumed edit were proof, proof dependencies, proof origin, Mathlib searches, status and split report. The statement, statement dependency, source, created record and complete blueprint ancestor/via chain were identical. The current item remains unsplit with zero proof steps, and it has no released repair-note file. I rebuilt the sandbox record from that current item and carried over only those split-owned fields. The required delivery tool independently builds its commit on the freshly fetched current server DAG. I have not marked the side completion as live completion or edited any maintainer-owned field.

For the citation recheck I opened the entire current statements of `def-weil-sheaf-of-modules-category` and `lem-weil-pbc-glue-sheaves-of-modules`. The former explicitly gives the sectionwise linear components needed in Step 1. The latter explicitly gives arbitrary open covers, all pairs including equal indices, the stated triple-cocycle composition order, and the global module together with all local comparison isomorphisms used in Step 3. Both existing quotes remain verbatim, and these two inputs are exactly the union of the proof-step uses. Neither current statement requires a new hypothesis or a different citation. No proof of a cited node is being used in place of its statement.

I reread Stacks `modules.tex`, Tag 01BC, `lemma-set-isomorphism-classes-finite-type-modules`, especially its no-repetition-cover and set-of-gluing-data argument, and `sheaves.tex`, Tags 00AL and 00AM, the compatible-sections construction and module equalizer argument. I also reread the current blueprint ancestor's finite-pushforward paragraph, the chapter and unit records, and the project gluing declarations. The project declarations still supply effectivity for a single datum rather than the item's full set of tuples; there is no exact attachment. The retained searches and their actual six Q80 receipts were read, and the limits and quasi-coherent-presentation hits were reopened. Their questions and the statement have not changed, so I retained them without invented or redundant searches.

The substantive witness-set clarification from the preceding repair is preserved and sharpened in Step 4: it now lists addition, negation, zero, scalar multiplication and every restriction map as functions, then imposes the module, restriction and sheaf axioms as predicates. Comparison isomorphisms include encoded inverse maps. This explicitly bounds the witness sets before choice without importing an unasserted construction from the gluing theorem. Steps 1 and 2 remain the elementary Hom/Iso and dependent-product encodings; Step 3 remains the existing effectivity theorem. No new node is needed, and no step exceeds 2000 characters. The empty-space/empty-cover, empty-label, empty-D and infinite-cover checks above still apply. No statement correction or route change is made.

The final dry run follows this resumed edit; the push will run only after that same process exits successfully. All writes remain in this sandbox, and no compiler, Lake command, local DAG/preflight checker or direct git command was run.


## Repair of current return L: 8a5542a91d3

The current return is dated 2026-10-22 12:46 UTC and names `8a5542a91d3`. The earlier return-head sections above are retained history, not the current repair request. After the interrupted provider call, the original tool session was unavailable and a process check showed no Q80 delivery still running; only then did I start the required dry run. It exited 0 and printed `OK (not pushed)` at `1688a886290`, so there is no overlapping delivery invocation.

I compared the retained returned node with the current shared DAG item field by field. The live item is `unsplit` with no proof and no released repair note. Only the six split-owned fields differ: proof, proof dependencies, proof origin, Mathlib searches, status and split report. The full statement, its statement dependency, source, chapter, unit, created record and blueprint ancestry/via/place agree. I rebuilt the sandbox JSON from that current live record and carried forward those six split-owned fields, retaining every existing argument, citation, search and report. The delivery tool fetches the current server DAG and creates its delivery there; I do not promote side-project completion or set any maintainer field.

I reopened both current cited statements in full. Step 1 uses exactly the definition's sectionwise linear sheaf morphisms, so its injection into a product of function sets needs no theorem about essential smallness. Step 2 uses that result and universe closure: the covers are subsets of the set of opens, the labels form dependent products, and the transition isomorphisms form products over all ordered pairs; covering and cocycle equations are predicates. Step 3 uses exactly clause (2) of the existing gluing theorem: arbitrary open covers, module sheaves on each member, isomorphisms on all pairs including equal indices, the stated triple-cocycle order, and global comparison isomorphisms in the required direction. Neither input's present statement changes the hypotheses needed by this proof. Both entries in `citations.json` remain literal substrings, and together they account for every node used by the proof.

This repair also makes two checks explicit in the proof itself: Step 3 now cancels an invertible diagonal transition in the all-equal cocycle to obtain the identity, and Step 4 explicitly takes the disjoint union of the witness sets over D before applying choice. These are elementary consequences of the displayed equations and set encodings, not new subclaims requiring nodes. Thus the repair is not an unchanged re-push. The single-datum gluing theorem is not used for a construction hidden inside its proof. The universe enlargement bounds witness choices while each selected sheaf retains sections in the fixed original universe. The empty cover on the empty space, empty label sets, empty D, empty overlaps and infinite covers still satisfy the argument. No step exceeds 2000 characters.

I reread Stacks `modules.tex`, Tag 01BC, including the no-repetition covers and set of gluing data, and `sheaves.tex`, Tags 00AL and 00AM, including the compatible-sections formula and module equalizer. I read the current blueprint ancestor's finite-pushforward paragraph and the chapter/unit records. The project gluing and object-descent declarations still provide only single-datum effectivity, so they do not attach this parametrization theorem. The six actual Q80 search receipts and their results were reread, and the presentation and limit-smallness candidates reopened; no statement or search question changed, so no searches were repeated or invented. B--E have been rechecked: no new nodes, duplicated clauses, missing non-elementary input, cycle, additional hypothesis or statement change is introduced.

All edits are in this sandbox. No direct git command, Lean write, compiler, Lake, or local DAG/preflight checker was used. The final dry run must validate these edits before the authorized push.
