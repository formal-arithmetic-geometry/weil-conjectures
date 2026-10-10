# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-kflat-stalk-criterion.json`: split item with two proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-acyclic-stalk-detection.json`: new unsplit statement-only node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-stalk-tensor-complex.json`: new unsplit statement-only node; no Mathlib match.
- `citations.json`: verbatim citations for every step dependency.

## Attachments

None. I searched the slopmaster2 Lean source for the item id, its K-flat and stalk terminology, and the blueprint tag; no sorry-free project declaration states the item.

## WANTED

WANTED: `literature/stacks-project/cohomology.tex`, Cohomology Lemma Tag 06YB, for `lem-pc-kflat-stalk-criterion`, `lem-pc-acyclic-stalk-detection`, and `lem-pc-stalk-tensor-complex` (the source file is not present in this checkout).

## Not duplicates

`lem-pc-acyclic-stalk-detection` vs existing stalk exactness nodes: the existing nodes concern exactness of individual stalk functors or geometric etale stalks, whereas this node states acyclicity detection for arbitrary complexes of sheaves on a ringed space.

`lem-pc-stalk-tensor-complex` vs existing tensor and stalk nodes: existing nodes state the abstract total tensor construction or individual sheaf stalk formulas, whereas this node states the complex-level natural isomorphism between the stalk of the total tensor and the total tensor of stalk complexes.

`lem-pc-skyscraper-complex` vs `lem-weil-pbc-skyscraper-constant-on-point-closure` (009A): the existing node concerns sheaves of sets and identifies a skyscraper with a pushforward from a point closure; this node concerns complexes of modules on a ringed space, with germ-linear action, exactness of the termwise construction, and recovery of the stalk complex.

`lem-pc-skyscraper-complex` vs `lem-weil-pbc-module-skyscraper-stalk-adjunction` (009A): the existing node is the scheme case of the stalk/skyscraper adjunction for one module and does not state exactness or acyclicity for complexes; this node is for arbitrary ringed spaces and adds the complex-level acyclicity and stalk clauses.

## Review by C1

I read the target node and the existing `lem-pc-kflat-pullback-preservation` node, which uses both directions of this criterion. I also read `def-pc-kflat-complex`, `def-pc-acyclic-complex-modules`, and `def-pc-tensor-complex-sheaves` to verify the hypotheses and the exact meaning of K-flatness, acyclicity, and total tensor. The imported source is Tag 06YB; its text is absent locally, so the proof origin and the three nodes record the source gap explicitly.

Step 1 uses the K-flat definition, the new stalkwise acyclicity statement, and the new stalk-tensor isomorphism: these say respectively that tensoring with any acyclic sheaf complex is acyclic, that its stalks are acyclic, and that the stalk tensor is the tensor of stalks. Step 2 uses the same three statements in the reverse order: an acyclic sheaf complex has acyclic stalks, stalkwise K-flatness makes every stalk tensor acyclic, and acyclicity detection returns the global conclusion. I copied the exact used sentences into `citations.json` and checked that each cited node says the required clause.

I searched the whole DAG and blueprint before creating both children; no existing node states either generic fact. Mathlib searches were run for the item and each new node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. I checked the zero-complex and one-term complex cases informally: both directions reduce to the ordinary stalk criterion for acyclicity and tensoring. No Lean attachment exists, and no unrelated files were changed.

## What could not be finished

The two child lemmas remain statement-only for a later stage-1 worker because neither is available as a Mathlib declaration and the Stacks source file is unavailable locally.

## Second reading by C1

- Item statement: checked against Stacks Tag 06YB (Lemma 20.26.4, `lemma-check-K-flat-stalks`) hypothesis by hypothesis; the ringed-space, stalk, and K-flat clauses agree.
- Step 1: checked against the forward proof of Tag 06YB; repaired to test an arbitrary acyclic local complex via its skyscraper complex, then use stalk detection and the tensor-stalk isomorphism.
- Step 2: checked against the reverse proof of Tag 06YB; the cited stalk acyclicity and tensor identification give the conclusion for every acyclic sheaf complex.
- `lem-pc-acyclic-stalk-detection`: statement-only, self-contained, definitions cited, and tested on the zero and one-term complexes; no Mathlib declaration found.
- `lem-pc-stalk-tensor-complex`: statement-only, self-contained, total direct sums and differential stated, and tested on one-term complexes; no Mathlib declaration found.
- `lem-pc-skyscraper-complex`: statement-only, self-contained, termwise construction and stalk/acyclicity clauses stated; sectionwise exactness checked, and no Mathlib module-complex declaration found.

Changes made: corrected the item node's `created.item`; added the missing skyscraper-complex input; rewrote forward implication to quantify over arbitrary local acyclic complexes; updated proof dependencies and citations; recorded this second reading.
