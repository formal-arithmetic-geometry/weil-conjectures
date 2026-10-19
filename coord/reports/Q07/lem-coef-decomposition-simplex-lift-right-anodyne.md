# Q07 stage-1 report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-decomposition-simplex-lift-right-anodyne.json`: item, statement preserved; five-step split; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-decomposition-simplex-attachment.json`: new statement-only lemma, unsplit, not a Mathlib leaf. It gives two combinatorial attaching pushouts without any contractibility or right-anodyne conclusion.
- `citations.json`: every use in every numbered proof step, with a verbatim excerpt from the cited statement.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint tag, decomposition/simplex-lift names and notions found no declaration of this criterion or of the new attachment lemma. Upstream master is reference material, not proof evidence. No Lean was written and no compiler, Lake or build tool was run.

## Wanted sources

WANTED: Jacob Lurie, Higher Topos Theory, Notations 4.2.3.1 and 4.2.3.7, Lemmas 4.2.3.5-6 and Proposition 4.2.3.8, printed pp. 248-252, for both delivered nodes. A repository archival copy is missing. The Harvard URL returned 403; the IAS URL `https://www.math.ias.edu/~lurie/papers/highertopoi.pdf` succeeded. I read the actual PDF, with the extract saved only in this sandbox as `HTT-extract.txt`. The repository literature files were not changed. The expanded argument is conservatively marked `proof_origin.by = agent`. There is no Stacks tag for the decomposition attachment theorem. The independent unique-root input has Stacks Tag 017R, `lemma-splitting-simplicial-sets` in `simplicial.tex`, and is already a Mathlib leaf.

## Problems and corrections

The imported item already had a plausible full argument but was `unsplit`. Its nondegenerate and degenerate successor steps were over 2000 characters and hid the assertions that characteristic joins give pushout squares, including noninjective characteristic maps. Those are actual comparison lemmas, not one-line consequences of a definition. I extracted precisely these comparisons into one new statement-only node and left the filtration, hypothesis checks, the two existing right-anodyne join applications and saturation in the item's proof. The new statement contains no proof sketch. The item is not reduced to applying a copy of itself: the new node contains no weak-equivalence hypothesis, contractibility hypothesis or right-anodyne conclusion.

The item statement agrees with HTT Proposition 4.2.3.8; no statement dispute or source correction was necessary. Its generality is essential: the base and lifts need not be quasicategories, the diagram need not be a poset, and the structural maps need not be monomorphisms. No hypothesis was added. I kept every inherited metadata field. The blueprint ancestor and via chain are retained, with explicit new-node ancestry; no chapter or unit route was changed. This node is auxiliary foundational infrastructure for the existing paragraph-2 adjunction route, not a change to the six-functor unit.

## Not duplicates

lem-coef-decomposition-simplex-attachment vs lem-coef-decomposition-simplex-lift-right-anodyne: the new node identifies two pushout squares for one simplex, with no homotopy assumptions or anodyne conclusion; the item assembles all simplices using homotopy assumptions and saturation.

lem-coef-decomposition-simplex-attachment vs lem-coef-decomposition-local-colimit-cocones: the existing node defines the same decomposition object but concludes a restriction equivalence of coherent cocone spaces; it does not state the lower-simplex attachment comparisons. Its proof filters by upper nerve simplices instead.

lem-coef-decomposition-simplex-attachment vs lem-coef-directed-decomposition-right-anodyne: the existing statement concerns only a directed poset of inclusions and concludes right anodyneness of the total inclusion. It does not give the pushout comparison for arbitrary diagram maps and degenerate lifts.

lem-coef-decomposition-simplex-attachment vs lem-coef-cofibrant-subset-colimit-decomposition: the existing statement is a finite-subset diagram colimit formula, not the two-block decomposition or a lift-category attachment.

lem-coef-decomposition-simplex-attachment vs lem-coef-join-pushout-right-anodyne: the existing node proves right anodyneness of an abstract Leibniz join under a weak-equivalence hypothesis; it does not identify that join's pushout with a decomposition filtration successor.

lem-coef-decomposition-simplex-attachment vs lem-coef-contractible-join-right-anodyne: the existing node proves right anodyneness for a join with a contractible right factor; the new node supplies the separate structural comparison.

Whole-DAG and blueprint searches used `4.2.3.8`, `decomposition simplex`, `simplex attachment`, `lift category`, and the decomposition/face-stability vocabulary. No blueprint statement duplicates the new lemma (`same_as: []`). The completed/source statements above were opened and compared, rather than their proof content being used as if it were a statement. No same-Stacks-tag pair arises: the new node cites HTT, not a Stacks source.

## Review by Q07

I read the unit and chapter, the current blueprint ancestor proof, the worker contract and delivery-errors B through E. For both the item and its child I read HTT printed p. 252 in the IAS PDF, with pp. 248-251 for the object, lift categories, and join conventions. Notation 4.2.3.7 defines exactly the full subcategory of degenerate lifts used here; Proposition 4.2.3.8 has exactly the two hypotheses of the item. Lemmas 4.2.3.5 and 4.2.3.6 have the right-factor orientation required by the two successor cases. No SGA reference is used.

Step 1 uses the statement of the unique nondegenerate decomposition node to take roots in K_F, not just roots in K. The local-colimit node's statement supplies the actual block operators. The child's statement supplies the definition by generated nondegenerate simplices, which the step identifies with the explicit root membership test. I checked closure under faces: deleting vertices acts on the blocks; a root's lower degeneracy surjection has the monotone section choosing the least member of every fiber, so the new lower simplex is a face of the previous one. When the upper block vanishes, the same argument removes additional degeneracies of the base simplex. This is an explicit combinatorial argument, not an appeal to an unstated theorem.

Step 2 uses only well-ordering of small sets and Step 1's membership test. The order includes degenerate base simplices, since their lifts may be nondegenerate. Every face is earlier in dimension, and limit membership is witnessed by one root. These observations explicitly verify the face and continuity hypotheses for all later applications. This step is elementary; it does not assert an uncited homotopy theorem.

Step 3 uses the child's nondegenerate pushout clause and exactly the statement of the contractible-join node with boundary inclusion on the left and N(I_sigma) on the right. Weak contractibility is supplied by the item's hypothesis, with no Kan condition. Step 4 uses the child's degenerate pushout clause and the statement of the Leibniz-join node. The nerve definition in def-cbc-enhanced-diagrams-cones makes full-subcategory nerve maps degreewise injective; the second item hypothesis supplies their weak equivalence. Thus both monomorphism assumptions of that join theorem have been checked. I included verbatim quotes for every citation rather than using a proof hidden below a cited node.

Step 5 uses precisely the pushout and transfinite-composition closure clauses in the right-anodyne definition, after verifying smallness and continuity in Step 2. The composite's endpoints are the pure-upper nerve and the entire decomposition. These are all the non-elementary inputs of the item's argument.

For the new child I tested m=0 (boundary empty, nondegenerate vertex attachment), degenerate m=1 (the pure lower simplex is already present), empty lift categories, B_0 empty, identity diagrams, and noninjective maps K_a to K. The join convention X star empty = X is crucial in the degenerate case, where it retains the old pure lower factor even if no degenerate lift exists. I also checked the combinatorial mechanism before isolating this lemma: mixed nondegenerate simplices have nondegenerate first lift and nonidentity upper arrows; a degenerate first lift gives a simultaneous lower-block degeneracy of all subsequent lifts. Characteristic join simplices outside the attaching domain are uniquely the new nondegenerate simplices, while identifications on the old domain are allowed. This is why generic Mathlib subcomplex pushouts alone do not settle this comparison.

I read each logged search and its actual service status. Prior sandbox searches were reused, and fresh searches tested both the attachment statement and the full criterion. The failed Loogle identifier is marked unavailable; the corrected CategoryTheory.IsPushout query returns generic subcomplex, skeleton and horn squares, none of which supplies the lift-category comparison in one line. I read SubcomplexColimits.lean, the skeleton definitions and root argument, and HomotopyCat.lean. The all-horn Quillen class returned for the criterion is not the right-anodyne criterion. The new node is therefore unsplit, not falsely labelled Mathlib. Its searches exactly match searches.jsonl.

I checked B1-B10 (statement-only self-contained child, TeX, honest sources/searches, blueprint fields, no attachment), C1-C8 (all non-elementary facts cited, statements read, no intended cycle, generic definition and Mathlib tools declared), D1-D5 (the child is a structural comparison, not the conclusion), and E1-E7 (hypotheses, dimensions, actual maps and degenerate edge cases). Every final proof step is under 2000 characters; no long inline comparison remains. Nothing is left unfinished in this one-level split; the new statement-only child is intentionally queued for a later split.

Resumption audit (2026-10-17): I retained the prior split and all logged searches. The initial required dry run exited 0 with preflight passed at 22c911d6b8. Comparing with the current repository found no change to the item statement, hypotheses, unit, ancestry or cited statements; every citation quote still matched. I reread the retained IAS HTT extract (Notations 4.2.3.1 and 4.2.3.7, Lemmas 4.2.3.5–6 and Proposition 4.2.3.8), the Stacks splitting proof and Mathlib SubcomplexColimits.lean:82–99, Skeleton.lean:1–115 and HomotopyCat.lean:1–80. I corrected the missing TeX row separators in both new-node pushout squares and refreshed the affected citation quotes. This changes only presentation of the same specified maps. I also corrected the recorded line range for the generic Mathlib pushout candidate. All five item proof steps remain below 2000 characters (1107, 682, 656, 1082 and 442). No additional search or Lean compilation was needed for these presentation corrections.

For B3 I made the ordinary simplex boundary convention explicit in the child: its simplices are the monotone maps with nonsurjective image. This is the boundary already used in the source and in the logged searches, including the empty boundary for m=0; no mathematical statement or search question changed.
