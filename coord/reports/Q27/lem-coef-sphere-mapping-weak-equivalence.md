# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-sphere-mapping-weak-equivalence.json`: split item, eight complete proof steps; statement unchanged; no new DAG nodes and no new Mathlib leaves.
- `citations.json`: verbatim passages for every cited node in every proof step.
- `rewrite.py`: sandbox-only JSON editing helper; not part of the delivery.

## Attachments

None. Searches for the item id, the blueprint tag, sphere maps, compact-open mapping spaces, and weak homotopy equivalences in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration stating the item. Upstream master was inspected as reference only, not as evidence of a finished proof. There is no Lean audit entry on the assigned node requiring extraction of an open declaration.

## WANTED

WANTED: Mark Hovey, *Model Categories*, Lemmas 2.4.13–2.4.17 and Definition 2.4.21 / Proposition 2.4.22(1), printed pp. 55–58, for lem-coef-sphere-mapping-weak-equivalence. The source URL in the assigned node was opened and read online, including the full proof of Lemma 2.4.17 and its preceding lemmas; no source was downloaded or written to the repository. Hovey is not archived in the project's literature directory. Accordingly `proof_origin.by` is `agent`: the existing source attribution is retained, while the actual retraction, shell, group chases, and low-degree argument are written out in the item. There is no relevant Stacks tag, and no SGA source is used.

## Errors and corrections

The assigned statement is correct as written, including arbitrary topological target spaces and the empty sphere. No STATEMENT-DISPUTED correction was needed.

The earlier sandbox attempt introduced `lem-coef-serre-model-mapping-invariance`, a general-cofibrant-source mapping-space assertion, and then applied it to the sphere. That moved the mathematical content into a restatement/generalization rather than splitting it (D1/D2). Its attribution to Hovey Lemma 2.4.17 was also inaccurate: that lemma states precisely the sphere case and proves it by induction, not by an already established Serre model structure. Moreover, the Serre-model node already uses this item, so citing that model structure would be circular. I removed this never-landed sandbox prototype and rewrote the item from the inductive proof. No existing repository node was deleted.

The former step 2 claimed an unkified compact-open conclusion from a child whose statement was already kified; its citation was therefore inaccurate. The replacement works consistently in k-spaces, proving the comparison with arbitrary spaces first. The former review said it cited the topological Serre-model node even though the proof no longer did so; that stale report has been replaced.

The current blueprint paragraph was read in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Its paragraph 2 is the derived coefficient adjunction and displayed derived inverse-limit calculation. The item is a foundational descendant via the inherited frame/Serre-model ancestry, not a direct assertion of that paragraph. The recorded ancestor and via chain are preserved and the exact supporting place is filled. The unit and chapter records were read; this auxiliary item is not the unit's key statement, so no unit realization is changed.

## Mathlib and duplicate search

The item was searched with the prescribed `msearch.py` command using LeanFinder, Loogle, grep and LeanSearch, with a second semantic phrasing and a second weak-homotopy grep. Queries and actual results are preserved in `searches.jsonl`; the new item records quote the real log entries. The natural-language Loogle attempt returned an identifier error and was followed by the valid `"WeakHomotopyEquiv", ContinuousMap` query, which returned no hits. Semantic hits such as `HomotopicalAlgebra.LeftHomotopyClass.postcomp_bijective_of_weakEquivalence` assert bijectivity on abstract left-homotopy classes in a model category, not an equivalence of topological compact-open mapping spaces. The supplied types and follow-up Mathlib grep were read. The loop-group search found definitions and an iterated-loop/fundamental-group equivalence, not the item. Thus the item is not a Mathlib leaf.

Whole-DAG keyword searches and `tools/blueprint_refs.py search` for sphere mapping weak equivalence, Serre fibration, homotopy extension and compact-open were read. The existing `lem-coef-serre-homotopy-exact-sequence` is the independent input needed for the published induction; the existing `lem-coef-compact-open-currying` is a Mathlib leaf and gives both directions of the exponential law. No duplicate or new node is necessary. `blueprint.same_as` is empty because none of the blueprint statements states this topological sphere theorem.

## Not duplicates

No new node is delivered. The old `lem-coef-serre-model-mapping-invariance` prototype was removed from this sandbox rather than delivered.

## Review by Q27

I read Hovey's proof at the cited URL and every statement cited in the eight replacement steps, and checked the argument against B–E of `coord/delivery-errors.md`. The crucial source facts and hypotheses are as follows.

Step 1 uses `lem-coef-realization-finite-limits` only for the final compact-Hausdorff test topology and the k-space limit description, and `lem-coef-compact-open-currying` for its continuous transpose and continuous evaluation clauses. Both clauses apply because disks, spheres, and the compact Hausdorff parameter products are locally compact where required. The component and cube-homotopy convention is the explicit last portion of the first paragraph of `def-cbc-enhanced-diagrams-cones`, not its separate simplicial weak-equivalence definition. The final-topology test proves, rather than assumes, that replacing X and Y by their kifications changes none of the mapping-space homotopy tests.

Step 2 proves the restriction lifting property with an actual formula R, so no undeclared fibration theorem is used. I checked that the denominator is positive, the image lands in the bottom or side, both subsets are fixed, and pasting and currying supply the full continuous disk-parameter lift. Step 3 writes the disk contraction and the moving-basepoint shell explicitly. This is essential because a homotopy that contracts the disk does not fix an arbitrary map as basepoint. Its constant-map case is based; the shell and its reverse give the needed comparison at all other basepoints, naturally in Z. No use is made of `lem-coef-homotopy-groups-basepoint-change`, since its unnecessary Kan-model statement dependency would create a cycle here.

Step 4 uses the same exponential law and k-limit statement to establish the sphere mapping pullback; it writes the disk-quotient map and deduces the evaluation lifting property from step 2. Step 5 uses the two directions of currying to identify paths in the based-map fibre with relative homotopies and the explicit radial cube/disk map to identify its components with the homotopy groups from the definition node. The r=0 fibre is X itself, not a positive homotopy group.

Steps 6 and 7 use the natural exact sequence in `lem-coef-serre-homotopy-exact-sequence`. The node states the exact group segment and functoriality actually used. Its hypotheses hold for the k-space restriction and evaluation fibrations proved in steps 2 and 4. I wrote the kernel/image chase in both directions rather than invoking an unproved five lemma, and checked the nonabelian j=1 case using products. For the evaluation comparison at j=1, the final term is the pointed set of fibre components; step 5 supplies exactly the required injection at the distinguished component.

Step 8 uses the same node's explicit natural loop-action and orbit-set description. A group isomorphism and an equivariant set bijection give a bijection on orbit sets by the short written representative argument. This handles all components over each base component and uses the original bijection on base components to assemble the result. It does not treat pi_0 as a group or assume connectedness.

Small cases checked: r=-1 gives singleton mapping spaces even for an empty target; r=0 gives X×X and its evaluation fibre X; m=0 gives the empty-boundary disk restriction; X empty forces Y empty by the given component bijection, with empty nonempty-sphere mapping spaces. Fibres at nonconstant sphere maps are allowed throughout the group chases. No surjectivity on points of f is assumed. The inductive hypothesis is explicitly the full assertion at r-1 before either fibre chase uses it.

Every step's `uses` was checked against the cited statement and a verbatim excerpt is in `citations.json`. The only off-unit tool declaration is the shared cubical homotopy definition. `proof_deps` is the union of the uses. New-node form and search requirements are vacuous after removing the prototype; all inherited maintainer fields remain in the copied item. The statement has not been weakened and no target or definition has been changed.

## What remains

No mathematical gap or unsplit child remains in this split. The sandbox awaits the required dry run and a fresh second reader; it must not be pushed by this worker.

## Search-tool invocation correction

Four exploratory searches for the discarded child were initially invoked with the child's id in msearch's item argument, which put their tool-managed log under a sibling sandbox. That was an invocation error: the authorized item argument is `lem-coef-sphere-mapping-weak-equivalence`. I corrected subsequent calls to use this item's sandbox, used only those real parent-item log entries for the updated proof, and delivered no child node or child search claim. No project or launcher file was edited.

## Second reading by Q27

- Statement: checked against Hovey, Model Categories, Lemma 2.4.17 (pp. 56–57) and Proposition 2.4.22(1) (pp. 57–58); the component, positive-group, sphere convention, kification, and empty-sphere clauses agree, including the cases (r=-1), (r=0), and empty spaces.
- Step 1: checked the kification reduction against the realization finite-limit statement, compact-open currying, and the explicit cubical homotopy-group definition; the compact-Hausdorff test argument supplies both directions and no extra hypothesis is used.
- Step 2: checked the displayed retraction (R), its denominator, boundary values, and the currying/pasting argument against the compact-open node; the (m=0) case is included and the Serre lifting property is established directly.
- Step 3: checked evaluation, constant section, disk contraction, and the moving-basepoint shell against compact-open currying and the cubical definition; the shell supplies the missing arbitrary-basepoint argument and is natural under postcomposition.
- Step 4: checked the disk-boundary quotient model of (S^r), the k-space pullback, and evaluation lifting against the finite-limit and currying statements; (r=0) is handled explicitly and no dependent Serre-model theorem is invoked.
- Step 5: checked fibre identification (in particular the circle case gives based loops), relative disk homotopies, the radial cube/disk homeomorphism, and the (r=0) fibre (F_X(x)=X) against currying and the cubical definition; the stated component bijection uses exactly the hypotheses on (f).
- Step 6: checked the restriction-fibration exact-sequence chase against the full statement of `lem-coef-serre-homotopy-exact-sequence`; total-space and base maps have the required hypotheses from Steps 3 and 4/induction, and the (j=1) product case is written.
- Step 7: checked the evaluation-fibration exact-sequence chase and the pointed-set (j=1) case against the same exact-sequence statement; Step 6 supplies the fibre maps and the original (f) supplies the base maps at every basepoint.
- Step 8: checked the loop-action orbit-set argument, stabilizers, and assembly over components against the exact-sequence node; no connectedness or group structure on (pi_0) is assumed, and the empty-space case is addressed.
- New nodes: none; the discarded general-cofibrant-source prototype is absent, so there are no B1–B7 or duplicate-node repairs to make. Existing-node searches and Mathlib searches are recorded in the worker report and `searches.jsonl`.
- Changes made: expanded Step 3 with an explicit boundary-fixed cubical homotopy connecting disk contraction to the moving-basepoint shell, so its claimed compatibility is checkable rather than implicit (E5); made Step 4’s compact quotient use the disjoint union with the marked point, explicitly covering the two-point case (E4/E5); removed the worker-written `split_report.tool_uses` entry, leaving the off-unit tool request in the report for maintainer review (C8). Appended this audit. No statement or dependency changed; inherited creation metadata stays intact. The existing citations still quote exactly the statements these repaired steps use.

Second-reader independent Mathlib search: `msearch.py Q27 lem-coef-sphere-mapping-weak-equivalence leanfinder "Mapping a sphere into spaces preserves isomorphisms on homotopy groups and path components"` returned eight hits, including `HomotopyGroup.Pi`, fundamental-group induced maps and fundamental-groupoid homotopy invariance. Their returned types define groups/maps or concern degree one; none states this mapping-space weak-equivalence theorem. The actual output is in `searches.jsonl`.
