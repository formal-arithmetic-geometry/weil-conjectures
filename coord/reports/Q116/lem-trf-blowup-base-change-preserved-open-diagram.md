# Stage-1 delivery: lem-trf-blowup-base-change-preserved-open-diagram

## Files written

- dag/nodes/sec-trace-formula/lem-trf-blowup-base-change-preserved-open-diagram.json: statement, split into five proof steps; no complete Mathlib match.
- citations.json: thirteen entries, one verbatim statement quotation for each node cited in each step.
- report.md: this report. searches.jsonl contains the actual recorded searches. prepare.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit realization is changed: this derived item is not the unit's key statement.

## Attachments

None for the item. I searched the blueprint tag and the blowup/strict-transform/preserved-open notions in lean/WeilConjectures. FlatBaseChange.lean supplies the blowup isomorphism and its W projection; Complement.lean supplies the complement isomorphism. Neither declares all the ambient and restricted closed-immersion diagram clauses. I reuse the existing attached DAG nodes rather than claim an attachment for this item.

## WANTED

None. The sources needed here are present in literature/stacks-project. The inherited brief's coord/dag-sync.md is absent; the current direct-delivery instructions govern this task.

## Corrections and scope

The statement is unchanged; there is no statement dispute. There was no previous sandbox split or report to repair. All inherited item metadata and earlier Mathlib search entries are preserved. The existing statement dependencies are all used in the statement. The imported proof was empty. The nearest blueprint ancestor is lem-trf-local-term-locality, through the recorded strict-transform chain; the latest blueprint ancestor proof addresses contraction and does not itself state this blowup diagram. I read that current proof and the latest flat-base-change and complement nodes. This delivery realizes the already extracted geometric subargument, and does not alter the chapter or unit route.

The proof uses the exact specified comparison, not an arbitrary isomorphism of the blowup schemes. In particular Step 2 uses the comparison theorem's phrase "is an isomorphism over Y" and writes the equation on the W projection. The final equality is an equality of maps into P_W, checked on both projections. No SGA source is used.

## Not duplicates

No new nodes are created. DAG and blueprint searches for blowup, blowing, base-change, preserved, comap, complement of the center, and closed immersion identified existing interfaces. The affine ideal-extension, zero-locus, complement, comparison and closed-immersion facts are reused. The generic associativity/isomorphism/restriction calculations remain elementary proof steps rather than new clause-restatement nodes.

## Review by Q116

I read Stacks divisors.tex Tag 0805 (lemma-flat-base-change-blowing-up), including its proof via pulled-back Rees powers and relative Proj, and Tag 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), including the proof of its first clause. For the restrictions and closed immersions I read schemes.tex Tags 01JR (lemma-open-fibre-product), 01JU (lemma-fibre-product-immersion), 01JX (definition-base-change), 01JY (lemma-base-change-immersion), and 01IN (lemma-closed-subspace-scheme); I also read morphisms.tex Tag 01QR (lemma-base-change-closed-immersion). There are no new nodes requiring separate literature sources.

For Step 1, I opened def-nagata-extended-ideal: its definition is the ideal of the base-changed center. I opened lem-pc-ideal-sheaf-comap-affine-extension: it explicitly gives the generated ideal IB on every affine chart B_0 lying above A_0, with no flatness or Noetherian assumption. I opened lem-weil-pbc-closed-immersion-image-zero-locus: its statement gives membership in V(I) by containment in the point's prime on an affine open, and applies to both centers. I opened def-weil-affine-spectrum for the contravariant affine morphism; on prime ideals its defining map is contraction. Consequently IB lies in q exactly when I lies in the contracted prime. This proves equality of underlying opens, and the restrictions of O_W give equality as open subschemes. The affine charts exist locally, so no global affine or quasi-separated assumption is introduced. I also read the upstream ideal_comap_appLE proof at IdealSheaf/Affine.lean:92-109 and Mathlib's comap/support_comap definitions and proof.

For Step 2, I opened thm-nagata-blowup-flat-base-change and its statement dependency def-nagata-blowup-flat-base-change-map. They specify exactly the comparison bc_v and assert it is an isomorphism over W; the latter definition puts W first, and our c exchanges factors. I also read FlatBaseChange.lean:141-164, which has the comparison, its inverse through asIso, and the W-projection identity. The morphism v is flat as required. I opened thm-nagata-global-blowup-complement and checked it states that the structure map restricted outside V(I) is invertible. It applies to I and I_W; the blowup construction accepts arbitrary quasi-coherent ideals, so no additional finiteness claim about I_W is needed. The open-preimage node explicitly identifies preimage opens with the relevant fibre products. Finally I wrote the inverse of the base-changed complement map and the equation a_{U,W} c_{U_W}=b_{U_W}; this forces the canonical comparison on the preserved open. I read Complement.lean:57-87 as a further check of the restriction convention.

For Step 3, the only cited statement is def-pc-fibre-product. I read its full universal property, uniqueness and induced-morphism clauses. Both displayed component lists have matching images in X and W. Applying c^{-1}c or cc^{-1} returns every projection, so the inverse formulas give inverse scheme morphisms. This is a direct use of the cited definition, without a hidden associativity theorem or a separate geometric comparison. The formulas keep z and w unchanged, giving the Z_W and W compatibilities.

For Step 4, I reopened the open-preimage node and fibre-product definition. The common-image factorization through U is precisely the condition defining U_W by Step 1. I specify both inverse maps using the inverses from Step 2. After theta their maps to R have the same z,w and U_W components, so uniqueness proves equality and both requested projection compatibilities. No assertion about scheme-theoretic closure, strict-transform base change, or irreducible components is used. This restriction argument is elementary once Steps 1-3 hold.

For Step 5, I opened lem-weil-pbc-closed-immersion-base-change: its statement permits any base morphism, with no finite-presentation or flatness requirement. It applies to i pulled back to P_W, to i pulled back to W, and to the resulting Z_W immersion pulled back to Q. The explicit T_W = Z x_X P_W identification is justified by the component lists from the fibre-product definition. I checked p theta = c widehat-p on its P and W components; this is the equality of the ambient diagram, not merely the abstract existence of an isomorphism.

I checked B-E of delivery-errors.md: no new statement-only nodes or notion definitions are needed, the citations are statements rather than proof internals, every non-elementary input is cited, and no item clause has been hidden in a new node. Each citation quote is a literal substring of its node's statement. All five steps are under 1000 characters, below the long-step threshold. I checked I=O_X (the two blowups and opens give the identity diagram), I=0 (the opens are empty), W empty, Z empty, v=id, Z=X, and a flat localization removing the center. The maps and equations still have their stated types and remain valid. Flatness is used only for the comparison theorem; the closed-immersion and open calculations need no stronger hypothesis. No new finite-type, separatedness, Noetherian or surjectivity assumption was added.

The off-unit affine ideal formula is a generic tool and is declared in split_report.tool_uses; the other off-unit results are Mathlib leaves or already closed. The server's preliminary review_split reports PASS with zero new nodes. The unfilled realization of sk-i-curve-zero belongs to its key-node worker, not to this item.

## Unfinished work

None in the one-level split. Existing dependency nodes retain their current status; no Lean was written or compiled, and no repository or launcher file was modified. Final delivery checks are recorded below when available.
