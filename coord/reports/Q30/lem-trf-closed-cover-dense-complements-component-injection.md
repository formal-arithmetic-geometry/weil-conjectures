## Files written

- dag/nodes/sec-trace-formula/lem-trf-closed-cover-dense-complements-component-injection.json: item, statement unchanged, split into five steps; not a Mathlib leaf.
- citations.json: verbatim statements for both dependency citations, indexed by proof step.
- No new nodes, hence no new Mathlib leaves. The split reuses two existing Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures by the blueprint tag and by closed covers, dense pairwise differences and component injections found no project declaration stating the item. Mathlib declarations are used through existing DAG nodes, not claimed as project attachments.

## WANTED

None. All sources used are present.

## What was wrong or missing

The item had no proof. I supplied the private-point construction, pointwise component existence, finite closed-cover containment, and injectivity argument. I retained its statement, statement dependencies, source and existing search history. No Lean, unit record, chapter record, repository or launcher file was written.

There is a source shorthand to interpret carefully: Stacks 0554's last paragraph says the intersections are “not dense”, whereas its earlier shrinking establishes “nowhere dense”. The stronger earlier assertion is what implies dense relative complements and is what the item correctly assumes. Mere nondensity would be insufficient: on a discrete four-point space the six two-point subsets cover, all pairwise intersections are nondense in either member, but there are only four irreducible components. This does not dispute the item's actual statement or require changing it.

## Unfinished work

None in this one-level split. Component existence already ends at a Mathlib leaf; the remaining inductions are written explicitly as elementary steps.

## Searches and reuse

Read the current latest blueprint (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), the item's unit and chapter, its ancestor lem-trf-local-term-locality proof, and the parent lem-trf-generic-fibre-component-lower-bound. The existing ancestry records the 0554 component-count input within the 055A/055B/05FH branch. This delivery only expands that local topological implication and does not alter the ancestor or its contracting-correspondence route.

Whole-DAG statement and Mathlib-match searches found lem-sc-irreducible-components-cover and def-weil-irreducible-components. I opened both complete files. Blueprint searches for “irreducible component”, “closed cover” and “dense complements” found no statement equivalent to this item; the closed-cover hit concerns coefficient models, not this topology assertion. No duplicate node was created.

Five searches were run through the prescribed msearch.py and preserved in searches.jsonl: LeanSearch, Loogle, grep, and two different LeanFinder phrasings. All services responded. I read the returned signatures and Mathlib/Topology/Irreducible.lean at lines 128, 148, 158 and 301--325. The component-existence hit is exactly the existing cover node. The finite-cover characterization supplies only one ingredient, while the other pertinent hits require Noetherianity or disjoint pieces. None states the whole private-point/component injection assertion or gives it by a one-line specialization. The inherited earlier search records remain unchanged.

## Not duplicates

No new nodes. Reused the existing component-cover and component-definition nodes instead of creating them; the dense-open and finite closed-cover inductions are elementary steps, not new lemmas.

## Review by Q30

I read Stacks more-morphisms.tex, Tag 0554, label lemma-irreducible-components-in-neighbourhood, including both the earlier nowhere-dense shrinking and the final component-count paragraph. For the maximal-component input I read topology.tex, Tag 004W, label lemma-irreducible, parts (3)--(4) and its Zorn argument. I also read Tag 004V, definition-irreducible-components, and Tag 0G2Y, lemma-pick-irreducible-components, whose first proof paragraph uses the finite closed-cover inference. No SGA source is used. There are no new nodes whose statements need independent source verification.

Step 1 cites nothing: the empty union is empty, so the empty families satisfy all conclusions. It handles the boundary case before any point is chosen.

Step 2 cites no theorem. I wrote the finite dense-open argument rather than treating it as a black box: in E_i, closedness of E_j makes each difference open; density ensures it meets every nonempty open, as proved by taking the closed complement of that open. The induction starts with the assumed nonempty E_i and stays nonempty and open. Finiteness of I terminates it. This proves simultaneous avoidance, not just a separate point for each pair. No irreducibility of E_i is used.

Step 3 cites lem-sc-irreducible-components-cover. Its statement explicitly says every point of an arbitrary topological space lies in an irreducible component, exactly the clause used to obtain K_i containing x_i. I checked that it has neither a Noetherian nor a sobriety hypothesis, and that it is a Mathlib leaf. Its statement, not any construction hidden in its proof, is enough; finite choice supplies the indexed family.

Step 4 cites def-weil-irreducible-components. Its statement explicitly gives nonemptiness and the binary closed-cover definition of irreducibility for subspaces. I wrote the finite induction: the empty cover contradicts nonemptiness; splitting off one member gives a binary closed cover, and the remaining finite union is closed. The induction therefore gives containment in one E_j. The already chosen private point forces j=i. This does not assert that E_i itself is a component or irreducible, and it does not claim the point's component is unique.

Step 5 cites nothing: if K_i=K_j with i different from j, Step 4 puts x_i in E_j, contrary to Step 2. This proves pairwise distinctness and the stated injection, with all containment clauses already established.

I checked B1--B10: no new unsplit nodes, the unchanged statement introduces its objects, its sole nonbasic notion cites its actual definition, and the added TeX uses single mathematical backslashes. During review I corrected the source tag of lemma-pick-irreducible-components to 0G2Y using the local tags table. Both existing Mathlib matches were read at their recorded declarations. Blueprint fields and original search records were retained, with actual current searches appended.

For C1--C8 and D1--D5, every non-elementary input is the quoted statement of the existing cover node. Both elementary inductions include their base and induction step; nothing was moved into a restatement node. citations.json contains verbatim text for every uses entry. Both dependencies are existing Mathlib leaves, so their other-unit placement is a permitted generic tool use and does not replace the unit's proof route. No reverse dependency on the item is introduced. All steps are below 2000 characters, and the two elementary inductions contain no hidden additional hypotheses.

For E1--E7 I checked empty I/T, singleton I with arbitrary nonempty reducible T, two meeting components, and a nonsober irreducible space. The singleton case uses the zero-length dense-open intersection and obtains any point-containing component; it does not force T irreducible. No generic points, separation conditions, Noetherianity, or irreducibility of covering pieces enter any step. Closedness is used for both relative openness and the component's closed cover; nonemptiness and finiteness are used exactly where recorded. The earlier versus final density wording of 0554 is addressed above. No statement correction was necessary.
