## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-two-ideal-adic-completeness.json`: split statement, five proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-complete-subideal.json`: new statement-only node; Mathlib searches found no exact criterion.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None.

## WANTED

None. The proof source is available in `literature/stacks-project/algebra.tex`.

## Not duplicates

- `lem-sfb-adic-complete-subideal` vs `lem-sbc-complete-local-subideal`: the new node applies to any commutative ring, any finitely generated ideal `L` contained in any ideal `K`, and assumes only `K`-adic completeness; the existing node is restricted to a Noetherian local ring complete for its maximal ideal and an arbitrary ideal inside that maximal ideal.
- `lem-sfb-two-ideal-adic-completeness` vs `lem-sbc-complete-local-subideal`: the item is the two-ideal quotient criterion for arbitrary Noetherian rings, while the existing node is the local subideal completeness special case and does not prove the quotient argument.

- `lem-sfb-adic-complete-subideal` vs `lem-per-local-support-completion-comparison`: the existing node proves degree-zero and degree-one comparison for derived local cohomology over a nonzero complete Noetherian local ring, with depth and support hypotheses; it cites 090T only as a prerequisite and does not state completeness for a smaller ideal in an arbitrary ring.

## What was checked and corrected

The imported item statement agrees with Stacks Tag 0DYC and was retained. The imported proof was empty, so I supplied the full Tag 0DYC route. I searched the DAG and latest blueprint for the quotient-completeness criterion and for Tag 090T; the existing DAG supplied the finite-module completion criterion (031D), completion modulo an ideal (05GG), completion as tensor product (00MA), Noetherian completion flatness (00MB), the Jacobson consequence of completeness (05GI), Nakayama (00DV), the faithful-flat maximal-ideal criterion (00HP), and faithful-flat ideal contraction (05CK). The only missing non-elementary input was the general finitely generated-subideal completeness statement, so I created the statement-only node `lem-sfb-adic-complete-subideal`.

## Review by Q49

I read the item source at `literature/stacks-project/algebra.tex`, Tag 0DYC, including all lines of its proof, and the latest blueprint unit/chapter material named by the imported node. Step 1 constructs the `(I+J)`-adic completion and uses exactly the statements of the completion-mod-ideal and finite-module completion nodes to identify its quotient by `I` with `R/I`; I checked the tensor quotient identification and the image of the canonical map. Step 2 verifies the hypotheses of the existing finite-over-complete-ring node: the completion is `I`-complete by the new 090T statement, its `I`-adic intersection vanishes, and its quotient is cyclic. Step 3 checks that the quotient module is finite, that the quotient identification gives `B=c(R)+IB`, and that Nakayama applies because the existing Jacobson node supplies containment of `I` in the Jacobson radical. Step 4 checks the flatness node, computes every maximal residue of `B` from `B/IB ≅ R/I`, applies the existing faithful-flat criterion, and then uses faithful-flat ideal contraction to obtain injectivity. Step 5 applies the new smaller-ideal completeness node to `J ⊆ I+J` after the established bijectivity. Every `uses` entry is backed by the corresponding verbatim statement in `citations.json`; `proof_deps` is the union of those uses. I tested edge cases conceptually: `I=0`, `J=0`, `I=J`, and nilpotent ideals all reduce to the stated completion argument. The Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`; none states the two-ideal criterion. No source error or statement correction was needed.

For the new node I read all of Tag 090T (lemma-complete-by-sub), including its principal-ideal reduction and convergent-series argument. The ring case is M=A of that source; it has no Noetherian or local hypothesis, and finite generation is required only of the smaller ideal. This is a real missing lemma, not a restatement of 0DYC: it assumes completeness for a larger ideal and has no quotient-completeness hypothesis. I checked L=0, L=K finitely generated, nilpotent L, and the zero ring; if K=A then the completeness assumption forces the ring to be zero. Both uses in the item have finite-generation witnesses: images of generators of I in B, and generators of J in R. The available upstream subideal proofs, including CompleteLocalSubideal.lean:33 and the private helper in CompletedQuotientCoverLift.lean:30, assume a Noetherian local ring complete at its maximal ideal and do not attach to this general node. The report declares the off-unit finite-over-complete-ring result as a generic tool in split_report.tool_uses. All five proof steps are below 2000 characters and hide no new sublemma: the quotient and cokernel computations are written out, and the non-elementary inputs have cited nodes.
