## Worker report

1. Files written: dag/nodes/sec-nagata-compactification/lem-weil-pbc-closed-immersion-from-composite.json (statement; exact Mathlib leaf), report.md and citations.json. No new nodes; one item converted to a Mathlib leaf. The four searches are recorded in searches.jsonl and in the item.
2. Attachments: none. The project search found uses of the Mathlib declaration, but no project declaration that states the item under exactly its hypotheses. IsClosedImmersion.of_comp_of_isSeparated in WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:83 instead assumes IsImmersion f and universal closedness of the composite; it does not directly state this item.
3. WANTED: none.
4. The imported statement is correct. Its proof was omitted, its same_as was unsearched, and it lacked a structured Mathlib match despite an old search and lead note naming one. I filled the match, searches and definition dependencies. No statement, target, unit or chapter was changed.
5. Nothing remains unfinished for this item. No Lean was written and no compiler or build tool was run.

## Not duplicates

No new node is created. The existing lem-weil-pbc-closed-immersion-cancellation has the same mathematical statement and is already a Mathlib leaf using the same declaration. It is not an imported blueprint node, so it is noted here rather than included in blueprint.same_as. Its lead note explicitly anticipates making this imported node a leaf as well. Neither existing node is edited or recreated. Whole-DAG and blueprint searches for closed immersion, closed immersion detected, closed immersion cancellation, and IsClosedImmersion.of_comp found no additional blueprint node to put in same_as.

## Review by NB

I read the chapter and proper-extension unit and both blueprint snapshots of this item. The main-20261015 statement agrees verbatim with the older statement; the older proof says Omitted. I read literature/stacks-project/morphisms.tex, lemma-immersion-permanence (Tag 07RK, verified in tags/tags), especially part (3) and its graph-factorization proof. It states exactly the cancellation assertion, without quasi-compactness, finiteness or reducedness assumptions.

For the item I ran LeanFinder, Loogle, grep and LeanSearch through msearch.py and read all their hits. All return AlgebraicGeometry.IsClosedImmersion.of_comp. I read Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:40 and 242-243. With X=T, Y=V, Z=S, f=r and g=p, the hypotheses are precisely that p composed with r is a closed immersion and that p is separated; the conclusion is that r is a closed immersion. The categorical notation f ≫ g has the required order. There are no extra typeclass conditions. The nearby comp_iff requires the second map itself to be a closed immersion and is not the match used here. The project theorem of_comp_of_isSeparated assumes an immersion separately, so I did not claim an attachment to it.

There are no proof steps and no new nodes to audit: a Mathlib leaf carries an empty proof. Consequently citations.json is the empty list, and there are no step citations or hidden non-elementary claims. I opened the three existing definition nodes: def-pc-scheme supplies schemes and their morphisms, def-weil-closed-immersion supplies closed immersions, and def-weil-proper-morphism explicitly defines separatedness by its diagonal. These are statement dependencies only, and all are existing Mathlib leaves. I also opened lem-weil-pbc-closed-immersion-cancellation and checked its statement and match, rather than creating another auxiliary node.

Small cases agree: the empty source and identity morphisms satisfy the same conclusion, and nonreduced schemes require no added assumption. Separatedness is essential in general: a chosen branch A¹ into the line with doubled origin has identity composite to A¹, while that branch is an open immersion with nonclosed image and the projection is not separated. The item retains that hypothesis. I checked delivery-errors B through E: no new-node form issues, no invented searches, no proof relabelling, no changed hypotheses or object identifications, no cycle introduced, and no long proof step. The only correction is metadata recognizing the exact existing Mathlib theorem.

The first dry run required an explicit proof_origin even for this Mathlib leaf. I supplied the documentary provenance Stacks Tag 07RK(3), which I had read, and retained the empty proof appropriate to a Mathlib leaf.
