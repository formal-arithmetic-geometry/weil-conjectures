# Stage-1 report: lem-trf-directed-tensor-least-support-stabilization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-directed-tensor-least-support-stabilization.json`: statement, now split in four steps; not a Mathlib leaf. The statement is unchanged. Existing searches are retained and six searches actually run for this delivery are appended.
- `citations.json`: six verbatim statement excerpts, covering every node citation in the four proof steps.
- `report.md`: this report. The search command maintains `searches.jsonl`.

No new nodes, no new Mathlib leaves, no Lean files, and no compiler or build calls.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, least-support/stabilization terminology and tensor/Mittag-Leffler terminology. The supported-perfect-complex stabilization declarations concern different objects. No project declaration found states this tensor-support result.

## WANTED

None. All proof sources were available locally.

## Corrections and dependencies

The imported item had an empty proof. I supplied the argument of Stacks Tag 059S with its final elementwise descent made explicit. There is no statement dispute: the generalization from finite free modules in 059S to arbitrary modules with the stated least supports is valid, because only tensor-colimit compatibility and leastness enter this part of that proof. No flatness is needed for an inclusion-induced map to have an image.

The statement dependencies remain `def-weil-pbc-category-colimit` and `def-weil-pbc-module-tensor-product`. The proof reuses the tensor definition and the existing Mathlib leaves `lem-weil-pbc-tensor-commutes-with-colimits` and `lem-weil-pbc-filtered-colimit-modules-elementwise`. The colimit recognition criterion is not used: its statement is a converse and would not supply representatives of a given colimit. Ring-colimit tensor lemmas are also not used, since the diagram here consists of modules over a fixed ring.

The current blueprint ancestor, its proof, and the current chapter and unit were read in `literature/blueprint/latest/`. The item retains the inherited supporting-algebra position beneath the local-term-locality route; no unit or chapter record is changed. Blueprint searches for `059S`, `least support`, `support` and `tensor colimit`, supplemented by DAG searches, found no blueprint node stating the item itself.

## Not duplicates

No new nodes were created. In particular, no node is introduced for support monotonicity, tensor-factor swapping, or the last containment argument: each is a few lines from the tensor universal property or leastness. The already existing general tensor-colimit and module-colimit elementwise nodes are cited instead of duplicated.

## Review by NN

I read `literature/stacks-project/algebra.tex`, Tag 059S (`lemma-flat-ML-criterion`), including the square and the entire last paragraph; Tag 00DD (`lemma-tensor-products-commute-with-limits`), including its coprojection compatibility; and Tags 00D6 and 00D7 (`lemma-directed-colimit`, `lemma-zero-directed-limit`), including the explicit eventual-equality description. The tag/label pairs were checked in `tags/tags`. These are sources for the item; there are no new-node sources to review.

For step 1 I opened the tensor definition node and checked that its statement gives the universal property, generation by pure tensors and induced maps. Evaluating both compositions on a pure tensor proves the square. A supporting preimage can therefore be mapped forward, without injecting the tensor of any submodule into the ambient tensor. Minimality of the supports assumed in the item gives both claimed containments. This is elementary and has its actual calculation written out.

For step 2 I opened the full statement of `lem-weil-pbc-tensor-commutes-with-colimits`. It supplies a colimit with its specified legs, for an arbitrary fixed module, not just finite or flat modules. It tensors the diagram on the opposite side from the notation in this item, so the proof explicitly constructs the swap and its inverse from bilinearity and checks compatibility on pure tensors. The defining universal property then transports the cocone. I opened `lem-weil-pbc-filtered-colimit-modules-elementwise` and checked that clause (1) really represents every element of any module colimit. Applied to the chosen preimage in Q tensor N, it supplies a stage h and its preimage v. Here Q need not be finitely generated. The index is small and filtered because it is the stated small nonempty directed poset.

For step 3 the equality clause (2) of that same elementwise node explicitly handles two elements from different stages and provides a common later stage with equal images. I used it on the H-tensor colimit established in step 2, at stages h and i. The output j is therefore above i as required. Mapping v in the Q-tensor diagram defines t, and the square from step 1 proves the exact equality with x_j. This avoids the invalid inference that a supporting lift must already equal x_h before passing to a further stage. Each invoked statement is quoted verbatim in `citations.json`.

Step 4 uses only the definition of least support and the two containments already proved in step 1. It concludes C_j = Q and then Q contained in C_k contained in C_j for every k above j. It does not assume the directed set is a chain or use a descending-chain condition. No additional non-elementary result is hidden here.

I checked delivery-errors B through E against these files: no new statement-only obligations or duplicate clauses, all notation is introduced in the item, all non-elementary facts have matching node citations, no new cycles are introduced (the proof dependencies are existing Mathlib leaves), and each tensor comparison is justified rather than asserted. The proof is 1788 characters, and no step exceeds 2000 characters.

I tested the zero tensor (all least supports are zero, choose t = 0), H = 0, a singleton index set (stage and colimit support agree), and the noninjective two-stage system Z to 0 with H = Z and x_0 = 1 (support drops from Z to 0 at the second stage). All conclusions have the right behavior. Tensoring 2Z included in Z with Z/2 illustrates why the inclusion-induced map need not be injective; the proof never uses such injectivity. Arbitrary directed posets are handled by the common upper stage given by the cited equality criterion, without countability. No extra hypothesis was added and no conclusion was weakened.

The Mathlib search hits were read: `TensorProduct.directLimitLeft` and `directLimitRight` give comparisons, while `Submodule.FG.lTensor/rTensor.directLimit` describe finitely generated submodule systems. They do not state eventual equality of given least supports. The second LeanFinder phrasing returned the representative and eventual-zero components, which are already covered by the two existing leaves. I inspected `LinearAlgebra/TensorProduct/DirectLimit.lean` and `RingTheory/TensorProduct/DirectLimitFG.lean` to confirm this distinction. The command's six exact log records are included in the item's searches; earlier records from the imported node are retained.

## Unfinished work

None in this stage-1 split. The maintainer's independent review remains part of the delivery protocol.
