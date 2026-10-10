1. Files written:

`dag/nodes/sec-picard-framework/lem-sc-pseudo-coherent-qcoh.json` (statement, split proof; no new nodes; Mathlib searches found no exact declaration).

2. Attachments: none.

3. WANTED: none.

4. What was checked and changed:

The item was not already stated by a sorry-free declaration in `WeilConjectures/`; the only source occurrence is an unrelated comment in `DirectImage.lean`. I read `/home/ubuntu/c1-stacks-review/perfect.tex`, Tag 08E5, Lemma 36.13.5 (`lemma-pseudo-coherent`), including its proof. The imported item source said 08EE, but the tags file confirms 08EE is the later lifting lemma; I corrected the item proof source and `proof_origin` to 08E5. The statement and its three definition dependencies were retained.

The sole step uses the pseudo-coherent local bounded-above finite-free model, the scheme setting, and the definition of `D_QCoh`. The cited definition statements say exactly these facts; the remaining argument is elementary: finite free sheaves are quasi-coherent, and cohomology is formed from kernels, images, and quotients, so the local cohomology sheaves are quasi-coherent. I tested the edge cases of the zero complex and a one-term finite free complex; both give quasi-coherent zero or finite free cohomology. No new lemma node is justified because the step is a direct two-to-three-line consequence of the cited definitions and the source proof.

The required searches were run with `msearch.py`: LeanFinder returned only generic derived-category and quasi-coherence declarations (no match), Loogle returned zero hits with unknown `PseudoCoherent`, Mathlib grep returned zero hits, and LeanSearch was unavailable. The exact queries and results are recorded in the node's `mathlib_searches`.

## Review by F1

I checked the source and definition dependencies line by line. Tag 08E5 states the local strictly perfect model and concludes quasi-coherence exactly as used. `def-pur-pseudo-coherent-complex` supplies the local bounded-above finite-free representative; `def-pc-derived-category` supplies the characterization of `D_QCoh` by quasi-coherent cohomology; `def-pc-scheme` supplies the ambient scheme hypothesis. The proof step has no hidden non-elementary dependency, and its hypotheses are exactly those in the item. I also checked that the child node `lem-sc-affine-pseudo-coherent-lift` uses this item for precisely the quasi-coherence reduction, so the split is not a duplicate or a restatement of that stronger affine lifting result.

## Second reading by F1

- Item statement: checked against Stacks Tag 08E5, Lemma 36.13.5, hypothesis by hypothesis; verdict: agrees, including the scheme, derived-category, and pseudo-coherence hypotheses and the conclusion that every cohomology sheaf is quasi-coherent.
- Step 1: checked against the statements of `def-pur-pseudo-coherent-complex`, `def-pc-derived-category`, and `def-pc-scheme`; verdict: the local bounded-above finite-free model and the definition of `D_{\\mathrm{QCoh}}` are cited, while finite-free quasi-coherence and closure under kernels, images, and quotients are a short elementary argument on a scheme.
- New nodes: none; no new statement requires a B1-B7 audit, and searches found no existing Mathlib declaration for the pseudo-coherent-to-quasi-coherent implication.
- Source and metadata: corrected all item and blueprint references from 08EE to 08E5, and corrected `created.item` to `lem-sc-pseudo-coherent-qcoh` so ownership matches the delivery.
- Edge cases: the zero complex and a one-term finite-free complex give quasi-coherent zero and finite-free cohomology; the argument also applies to the empty scheme.
