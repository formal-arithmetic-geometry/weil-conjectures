# Worker report: lem-sf-open-external-tensor-normalization

1. Files written:

- dag/nodes/sec-six-functors/lem-sf-open-external-tensor-normalization.json — statement unchanged, eight proof steps, no new nodes and no Mathlib leaves.
- citations.json — exact statement quotations for every cited node in every proof step.
- searches.jsonl — the actual msearch log retained from the interrupted preparation.

2. Attachments: none. I searched the read-only source checkout /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item id, title words, and relevant open-extension/tensor declarations; no sorry-free project declaration states the full item. The existing node lem-sf-open-tensor-normalization is a cited general input, not an attachment for this external-product statement. No upstream-master sorry declaration was used as a finished proof.

3. WANTED: none. The open extension-by-zero tensor calculation is available in literature/stacks-project/sites-cohomology.tex, Tag 0GL1; the simultaneous normalized external-product, signed-symmetry, and three-factor coherence formulation is agent-written from that source.

4. What was wrong or missing: the imported item was statement-only and needed its factorized construction, normalized composition comparison, restriction calculation, opposite-factorization comparison, signed symmetry, and three-factor coherence written as complete steps. I retained the hypotheses and statement exactly. No statement dispute, new helper node, hollow definition, or duplicate node was found.

5. Nothing in the natural-language split remains unfinished. I did not write Lean, invoke a compiler/Lake/build tool, or edit the live project.

## Review by NV

I read the chapter and unit records, the complete item statement and blueprint paragraph in literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, and the complete statements of every cited node. I also read the cited Stacks locations sites-cohomology.tex Tag 0GL1 and categories.tex Tags 0DV0 and 0B65. The finite coefficient ring is fixed throughout, and the ambient derived categories are the ordinary pro-etale module categories required by the cited normalization lemma.

Step 1 uses the statement of lem-sf-open-tensor-normalization: its open units are normalized on sections, extension by zero is fully faithful, and its beta and gamma maps restrict to identities. I checked that the finite constant-coefficient specialization in that statement matches the maps required by this item, so no intermediate constructibility hypothesis is silently introduced.

Step 2 uses the stated composite-adjunction construction def-weil-pbc-composite-adjunction and the unit-equation uniqueness in lem-weil-pbc-conjugate-iso-unit-equation, together with the open units from lem-sf-open-tensor-normalization. The comparison c(v,w): v_! w_! to (v w)_! is fixed by its unit, and the same unit argument proves the three-open associativity used later.

Step 3 checks the factorization through S = X x_B bar Y: u = j_1 k_1, r k_1 = p, and s k_1 = k q. The cited normalization statement supplies the Cartesian open base-change beta and the open projection/tensor gamma, so the displayed two arrows are exactly the claimed isomorphisms. I verified the projection identity bar q composed with j_1 equals s and the derived objects P = L r^* K and N_0 = L bar q^* k_! L.

Step 4 checks the second Cartesian square and the typed signed-tensor sequence. The first symmetry moves the k_1! factor to the front, gamma then applies with the correct arguments, and the second symmetry restores k_1^* P tensor Q = D. The statement of def-pc-tensor-complex-sheaves supplies the Koszul signed tensor used here. Every displayed arrow is invertible and natural.

Step 5 restricts the composite to T. The cited normalization statement supplies identity restrictions for beta and gamma, while Step 2 supplies the identity restriction for c. On homogeneous K-flat tensor sections the two symmetries multiply by (-1)^(ij) (-1)^(ji) = 1. The cited derived pullback and tensor-descent statements, lem-weil-pbc-ringed-topoi-derived-tensor-pullback and lem-weil-pbc-site-derived-tensor-descent, justify passing this chain-level calculation to derived categories and preserve the canonical associator and symmetry.

Step 6 uses full faithfulness from lem-sf-open-tensor-normalization to show restriction is faithful on maps with target u_!D'. I checked the conjugation by e(j,k)^-1, the unique representation u_!t, and the unit naturality argument. Reversing the two Cartesian squares gives the opposite factorization; its restriction is the identity by Step 5, so it equals the first construction.

Step 7 transports the construction through the factor swap. The left and right vertical maps are the signed external symmetries, and on the open they are the same Koszul map. The pullback/tensor and tensor-descent citations justify these derived identifications. Applying the Step 6 faithfulness argument proves the signed symmetry square, including its signs.

Step 8 applies the binary construction to three opens in the two parenthesizations. The tensor-pullback and tensor-descent statements justify the intermediate external products and common K-flat models. Each binary map and each normalized composition comparison restricts to the identity; the two associators agree on the same total tensor models. Full faithfulness then gives equality of the two composites. I checked the empty-open and identity-open edge cases; the construction is binary in arbitrary complexes, so no boundedness or constructibility claim is added.

I checked delivery-errors B–E: every non-elementary fact used by a step is a cited node, each cited node says the part used, all uses entries occur in proof_deps, and every citation quotation is copied verbatim from the cited statement. No new node is elementary, a duplicate, a restatement of the item, or a Mathlib leaf. The Mathlib searches recorded in searches.jsonl covered grep, LeanSearch, Loogle, and LeanFinder with two independent semantic phrasings; their hits concern generic presheaf tensors, zero products, or scheme restriction and do not state derived open extension-by-zero external tensor normalization. No Lean or compiler tool was run.

