# Stage 1 report

1. Files written: `dag/nodes/sec-picard-framework/lem-pc-derived-total-resolution-quasi-iso.json` (statement, no new nodes); `citations.json` (empty because the proof steps use only the item's stated hypotheses).
2. Attachments: none. No sorry-free declaration in `~/weil-conjectures-slopmaster2/WeilConjectures` carries the blueprint tag or the exact total-resolution statement.
3. The repository omits fetched literature, but the Stacks review checkout `/home/ubuntu/c1-stacks-review/homology.tex` supplies Homology Lemma 12.19.4 (Tag 09IZ), including the finite-support cancellation proof.
4. The imported node had no proof. I retained its statement and supplied the missing argument in three steps: cancellation in descending horizontal index proves surjectivity, the same argument after lifting a boundary proves injectivity, and the signed differential calculation concludes. The item is the direct Tag 09IZ criterion, so no smaller node was introduced; introducing a node for either cancellation would merely restate a clause of this item's theorem.
5. The statement and route were checked against Tag 09IZ in the review checkout, the dependent `lem-pc-derived-filtered-free-resolution` node, and the blueprint ancestor `lem-pc-projection-formula`.

## Review by J1

I read the item, its ancestor `lem-pc-projection-formula`, and the dependent filtered-resolution node. The item hypotheses give degreewise exact augmented rows and exact sequences of horizontal cycles; Step 1 uses exactly those two hypotheses to cancel every finite-support cocycle in the mapping cone, lowering the largest horizontal index at each correction. Step 2 checks the additional lifting needed when the image in `M^\bullet` is a boundary, then repeats the same cancellation to prove injectivity. Step 3 checks the usual signed total differential and combines the two cohomology assertions. No external node is cited, so `citations.json` is empty; the only non-elementary input is proved directly in Steps 1–2. I tested the formulation on the one-term resolution `A_0^\bullet=M^\bullet` (the total augmentation is the identity) and on an acyclic two-term complex, where the cancellation gives zero total cohomology. Mathlib searches were rerun for LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and the other searches found no matching total-resolution theorem.
## Second reading by J1

- Item statement: checked hypothesis by hypothesis against `/home/ubuntu/c1-stacks-review/homology.tex`, label `lemma-good-resolution-gives-qis` (Tag 09IZ); the ring-module version is the direct specialization of the abelian-group statement.
- Step 1: checked against Tag 09IZ proof, first paragraph; image and cohomology exact rows are explicitly obtained by splicing the displayed short exact sequences.
- Step 2: checked against Tag 09IZ proof, second paragraph; finite-support highest-index cancellation and termination are explicit.
- Step 3: checked against Tag 09IZ proof conclusion and the stated signed total differential; equality of classes and mixed-sign cancellation are stated directly.
- New nodes: none; the item is the sole statement node, so no B1-B7 auxiliary-node review applies. Existing dependency definitions were checked for cochain complexes and quasi-isomorphisms.
- Small cases: the zero complex and one-term split resolution give identity/zero cohomology; the finite-support argument has maximal index 0.

Changes: replaced vague mapping-cone and “same cancellation” prose with the source's image/cohomology-row derivation and explicit descending-index cancellation; updated proof sources to the available Stacks review checkout. No new node or citation was needed.
