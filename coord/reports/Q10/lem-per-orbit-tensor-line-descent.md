# Stage 1: lem-per-orbit-tensor-line-descent

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-orbit-tensor-line-descent.json`: item split, statement unchanged; not a Mathlib leaf.
- `citations.json`: seven entries covering every node used in every proof step, with verbatim statement excerpts.
- `searches.jsonl`: six actual Q10 searches made through the required msearch.py command. Their queries and returned summaries are also in the item, after the four inherited Q83 search records.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing 0BUT and tensor-calculus nodes suffice; a new invariant-frame lemma would only duplicate a short calculation in this item's proof.

## Attachments

None. Searched the live `lean/WeilConjectures/` source for the exact blueprint tag, orbit/tensor combinations and linearization/norm-line terminology. No project declaration states all of the item. Representation coinvariant declarations and a pullback-of-free-sheaf isomorphism do not give this descent statement.

## Literature

WANTED: local copy of Rydh, *Existence and properties of geometric quotients*, arXiv:0708.3333v2, Proposition 4.7, for the source record of lem-per-orbit-tensor-line-descent. The PDF is absent from this machine's literature directory. I read the proposition online at https://arxiv.org/pdf/0708.3333, printed pp.21–22. It discusses a norm line and its linearization in a broader quotient argument; it is not invoked as a theorem giving the precise assertion of this item.

The proof is marked `proof_origin.by = agent`. Its available local inputs are Stacks Divisors 0BUT (`divisors-lemma-finite-trivialize-invertible-upstairs`, divisors.tex 3617–3652), the local-frame route of 0BCY (`divisors-lemma-norm-invertible`, 3655–3696), and Modules 01CA/01CD/0B8L/01CT. I read the local Stacks text, including the pullback and tensor formulas. No literature files were written or downloaded.

## What needed repair

The item had a complete statement, empty proof and no proof dependencies. I retained its statement, original source, original search records, created record, and entire blueprint ancestry. There is no statement dispute or weakening. The proof now explains the local invariant generator, identifies invariant coefficients on every subopen, writes the evaluation and its inverse, and checks the actual tensor-power map, including degree zero.

The current `literature/blueprint/latest/` ancestor and its proof were read, together with the chapter and unit records. The orbit-tensor result is an auxiliary input created along the quotient branch, not the unit's key proposition. I also read the immediate parent's proof: Step 8 needs exactly the unchanged descent, equivariant evaluation and tensor-power clauses. That use remains valid. No unit realization fields need editing.

No unfinished mathematical part remains in the item. The required server dry run and push are performed by deliver.py after this report is written.

## Not duplicates

There are no new/existing-node pairs to compare because no new nodes are created. The whole-DAG searches found the exact local-trivialization tool `lem-sfb-finite-trivialize-invertible-upstairs` by tag 0BUT and the existing pullback/tensor and coherent-permutation tools; these were reused. The definitions and lemmas for pencil orbit norms and effective-action norm pencils do not state descent through an invariant-ring quotient: the former is a construction and the latter has integral/dominant hypotheses absent here. The normal-line-bundle power-linearization lemma concerns a connected algebraic group and a different assertion. None replaces this item.

Whole-blueprint searches with `tools/blueprint_refs.py search` for `orbit tensor`, `trivialize invertible`, `norm invertible`, and `line bundle descends` each returned no match. The ancestor command returned `lem-per-artin-gabber-affine-curve`. The item's precise inherited from.place was already filled, so I retained it and set same_as to the checked empty list.

## Review by Q10

I checked the split against delivery-errors B–E with every cited statement open. There are no new statement-only nodes, new names or speculative Mathlib leaves to audit. All object hypotheses are introduced by the unchanged item. Its existing statement dependencies cover schemes, finite morphisms, invertible modules, pullback, tensor and module sheaves. New proof dependencies are the union of the seven uses; every quote in citations.json was tested as a literal substring of the relevant live node statement.

Step 1 uses exactly the statement of `lem-sfb-finite-trivialize-invertible-upstairs`, read against Stacks 0BUT. It supplies an open neighborhood of each base point whose *whole inverse image* trivializes the given invertible sheaf. Finiteness of q and invertibility of L are item hypotheses; surjectivity is not needed here. Thus no unproved semilocal or simultaneous-trivialization argument is hidden in this step. The equality a_g^{-1}(q^{-1}T_i)=q^{-1}T_i follows directly from q a_g=q.

Step 2 uses `lem-weil-pbc-invertible-pullback-tensor`, clauses (1) and (2), for invertible translated factors, pullback/tensor comparisons, composition on pulled-back sections, and finite reordering. It also uses `lem-weil-pbc-module-tensor-symmetric-monoidal`, whose statement explicitly supplies coherent constraints and the action of any finite permutation on pure tensors. All modules concerned are invertible, so the first tool's hypotheses hold. I checked these statements against Modules 01CA, 01CD, 0B8L and 01CT. The new work is the explicit index calculation h -> hg -> hgk and the equality lambda_g(a_g^*n_i)=n_i, not an appeal to a general descent theorem. Right multiplication, rather than left multiplication, is necessary because pullback reverses composition. The local scalar actions follow the same composition of pullbacks, so this verifies maps, not just formal tensor symbols. This step is non-elementary because it invokes the two tensor tools.

Step 3 uses only the definition of a module sheaf. I wrote the gluing check: invariance of the glued section follows from uniqueness of the gluing after applying each group element. Multiplication by a base function preserves invariance because the map is over Y. This is an elementary consequence of the sheaf axioms and the hypothesis q a_h=q; it does not require exactness of fixed points.

Step 4 uses the local rank-one description in `def-sc-invertible-module`. I verified the actual formula on every W contained in T_i: f n_i is fixed if and only if f is fixed, by uniqueness of the coefficient of a free generator. The hypothesis O_Y(W)=O_X(q^{-1}W)^H then gives the unique b. This constructs an isomorphism of restricted sheaves, not merely a statement about the stalk or about sections on one affine. These local free rank-one presentations also witness quasi-coherence, so both parts of the definition of invertible module hold. No assumption that H acts freely or that its order is a unit enters the argument.

Step 5 uses the adjunction and explicit module-pullback definition in `def-pc-module-pullback`. The inclusion into q_*N has an adjoint; in local generators that adjoint sends b tensor m_i to b n_i and has the displayed inverse. These are formulas for the canonical evaluation, not an arbitrarily chosen isomorphism. Equivariance is checked on the generators fixed by both linearizations and then on their multiples, with the same pulled-back scalar. Local inverses agree by uniqueness and glue, directly from the sheaf axiom.

Step 6 uses the sheafification definition of tensor in `def-pur-sheaf-tensor-product`. Products of invariant sections give the actual multilinear map, so its sheafification is the map the statement asks about. In positive degree the invariant target has generator n_i^d and the source has generator m_i^d; sending one to the other proves invertibility of that particular map. In degree zero it is the original invariant-ring identification. I did not use a false general claim that invariants commute with tensor products, or assume that q is flat.

The three statement tools of other units are declared in split_report.tool_uses with their exact purpose. They are generic local-trivialization and tensor-calculus inputs; they do not replace a step of this unit's route. All other citations are definitions. I inspected all six steps for a hidden non-elementary subclaim and found none beyond the cited statements. The longest step is 826 characters, below the 2000-character review threshold. An extra node for any of the remaining coefficient or gluing calculations would be an elementary fact or a clause of this item, the faults described in B/C/D.

Small cases checked: H={1}, so the invariant-ring identification makes the local evaluation the usual identity; nonfaithful and trivial actions, where the permutation of repeated factors still fixes n_i; characteristic p with p dividing |H|, where the proof never divides by the order (for example the trivial C_p-action on Spec F_p); nonreduced schemes, since equality of coefficients in a free rank-one module remains valid over rings with nilpotents; Y and X empty, when the assertions are vacuous; and d=0 and d=1, which give respectively the given ring isomorphism and the definition of M. No normality, reducedness, flatness or Noetherian condition is used.

The six new search results were read. LeanSearch and LeanFinder returned representation coinvariants, ordinary invertible ring modules and the pullback of a free sheaf; these lack the finite scheme quotient and invariant frame. Loogle returned no hits. Both Mathlib greps returned unrelated elliptic-curve or representation linearization and manifold invariant-property sheaf material. A second phrasing was tried with LeanFinder and a broader grep. All six services/commands succeeded and the recorded queries are literal log entries; none is recorded as an unavailable service or an exact match.
