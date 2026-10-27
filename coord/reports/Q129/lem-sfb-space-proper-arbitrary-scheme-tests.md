## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-arbitrary-scheme-tests.json` (statement, split, no Mathlib match) and this report. `citations.json` supplies the verbatim statement evidence for every proof-step citation. The sandbox also retains `searches.jsonl` and its local preparation script.

## New nodes

None. Zero Mathlib leaves. All mathematical inputs already have DAG nodes.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, `AlgebraicSpace`, and algebraic-space terminology found no declaration that states this assertion. The node has no recorded project declaration. In particular no sorried project declaration was treated as a finished proof.

## Literature

WANTED: none.

The item follows Stacks `spaces-morphisms.tex`, Tag 083R, `lemma-proper-local`, equivalence (1) and (2). I read its statement and proof, `definition-proper`, and its four cited criteria: Tag 03KM (`lemma-separated-local`), Tag 040Y (`lemma-finite-type-local`, which concerns local finite type), Tag 03KG (`lemma-quasi-compact-local`), and Tag 03IT (`lemma-universally-closed-local`). For the forward implication I read Tag 04WP, `lemma-base-change-proper`. The universal-closedness argument expands the open-atlas argument of 03IT rather than treating a tag as a proof dependency. The point-map input already exists as `lem-a1-space-point-open-calculus`; I also checked the open-map statement in `spaces-properties.tex`, `lemma-etale-open`.

I read the chapter and unit records, the three-level route rules, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof. Its direct-image paragraph (3) is the recorded blueprint place above the inherited geometric/moduli chain. This small lemma supplies properness tests within that chain and changes none of the unit's coefficient categories or proof route. `blueprint.from.node` is null in the live item and in the ancestor tool's output; this existing ancestry is retained, including its exact place and via list.

## Searches and reuse

Before writing the split I searched the whole DAG for 083R, `lemma-proper-local`, its component locality labels, and algebraic-space properness, and used `tools/blueprint_refs.py search` for proper, universally closed, scheme tests and 03IT. The broad proper search includes scheme properness nodes but none states this assertion about arbitrary algebraic-space maps. I opened each selected node's statement and checked that its transitive dependencies do not reach this item.

Q129 ran the required logged Mathlib searches through `msearch.py`: LeanFinder with the full arbitrary-space equivalence and a second phrasing about separated, finite-type, universally closed maps and target atlases; LeanSearch with scheme base-change detection; Loogle with the strings AlgebraicSpace and Proper; and grep for algebraic-space terminology and proper base change in AlgebraicGeometry. All services answered. Results were schemes, including `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, `isProper_iff`, `isProper_eq`, and `UniversallyClosed` instances. I read `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, including the `Scheme` variables and base-change instance. These cannot specialize to arbitrary algebraic-space sources and targets. The live node's earlier Q53 search records are preserved, and Q129's queries/results are appended separately, matching `searches.jsonl`.

## Not duplicates

No new-node pairs arise. `lem-sfb-space-proper-base-change` proves only the forward permanence assertion. `lem-sfb-space-proper-fpqc-descent` and `lem-sfb-space-flat-proper-fp-locality` descend along covers of a scheme target; they do not state detection for an arbitrary algebraic-space target. `lem-sfb-space-representable-proper-tests` concerns maps representable by schemes and does not cover this item. The split uses the existing general chart/point tools instead of creating copies of these results or a node that restates the desired equivalence.

## Corrections and remaining work

The item's statement, statement dependencies, source, creation record and inherited blueprint provenance are unchanged. Its empty proof is replaced by five steps. No statement dispute, missing source, or uncompleted part was found. The proof deliberately retains quasi-compactness as a separate condition needed for finite type; local finite type alone is not silently called finite type. No new proof obligation is hidden in a statement-only node.

## Review by Q129

I reviewed this delivery against B through E with the node statements and the Stacks text open. The statement matches 083R hypothesis by hypothesis: a scheme S, arbitrary algebraic spaces X and Y over S, no representability of q by schemes, and all scheme maps into Y. Reversing the order of the sheaf fibre-product factors changes only the canonical presentation of the same projection. There is no Noetherian, finite-presentation, flatness or prior quasi-compactness hypothesis.

Step 1 cites `lem-sfb-space-proper-base-change`. Its statement expressly permits arbitrary algebraic spaces and arbitrary base change, so it gives every scheme test without an extra representability hypothesis. It does not depend on this item.

Step 2 uses the actual atlas in `def-trf-algebraic-space`, the separated/quasi-compact parts of properness in `def-sfb-space-morphism-properties`, and the equivalence in `lem-trf-space-qc-separated-etale-local`. The last statement explicitly covers a jointly surjective etale family from schemes, including the singleton atlas. Both properties hold for q_V, so the conjunction hypothesis of that criterion is satisfied. It concludes the conjunction for q; no separatedness or quasi-compactness is assumed beforehand.

Step 3 uses `lem-sfb-space-local-properties-chart-test` twice with its locally-of-finite-type choice. First the target is the scheme V, with identity chart, and the source chart is U over X_V. Its statement explicitly allows the identity target chart when the target is a scheme. Next V is the surjective target chart for q and U is the surjective chart of X times_Y V. Both applications have exactly the charts required by that node's statement. The conclusion is local finite type. The already proved quasi-compactness gives finite type by `def-sfb-space-morphism-properties`. This is the content of 040Y combined with 03KG, rather than a new finite-type lemma.

Step 4 fixes an arbitrary space Z over Y, not just a scheme. The algebraic-space/fibre-product definitions and `lem-trf-space-fibre-products-etale-covers` give E, its atlas base change, and the iterated fibre-product identification by the universal property. Only W must be a scheme, so the original hypothesis applies to X times_Y W. Properness therefore makes k closed. `lem-a1-space-point-open-calculus` expressly supplies continuity and surjectivity onto the set-theoretic point fibre product. For a closed C in E, its inverse image under r is closed and its k-image D is closed. The point-pair lifting statement, not a presumed homeomorphism of point fibre products, gives D = p^{-1}(h(C)). This checks the exact assertion used from that node and avoids assuming that point spaces preserve fibre products as sets.

Step 5 uses the same point-calculus node for openness of the representable etale atlas, and the algebraic-space definition for its surjectivity. The displayed complement equality follows directly from the preceding inverse-image equality and surjectivity. Its image is open, proving h(C) closed. This last inference is elementary and is written out, so there is no uncited topological descent lemma. The properness definition then assembles the three properties. Every cited statement has a verbatim entry in `citations.json`.

The two off-unit tool statements about point maps and quasi-compact/separated atlas tests are generic geometric tools, not replacements for a unit step. The split report declares these uses for the maintainer; it also declares the fibre-product tool already used by the statement. No maintainer-owned `tool_uses` field is written.

I tested the empty target and empty source cases: an empty target forces an empty source, singleton empty atlases are legitimate, and the closed-set complement calculation is valid for empty point sets. Identity maps satisfy both sides. When X and Y are schemes this specializes to the usual scheme assertion, but the proof never requires E or X_V to be schemes. Arbitrary non-quasi-compact Y is allowed because atlas criteria are local and do not require V to be quasi-compact. In particular no finite subcover, finite atlas, or affine-intersection assertion was used. All steps are under 2000 characters (the whole assembly proof is under 3000); no long step hides a separate lemma. There were no new statements to audit for small-case failures, no unrun searches recorded, and no changes to repository, launcher, Lean, or compilation state.
