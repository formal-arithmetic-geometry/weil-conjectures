# Q83 — lem-trf-finite-monoid-rational-coordinates

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-monoid-rational-coordinates.json — statement, now split in six elementary steps using two existing Mathlib leaves; no whole-item Mathlib match.
- citations.json — one verbatim statement excerpt for every step/node citation.
- searches.jsonl — six actual Q83 search results, retained with the earlier Q62 searches in the item.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures by the blueprint tag and by finite-monoid, rational-coordinate and tensor/basis concepts. The finite-monoid action declarations concern scheme quotients, not this item. No exact proved project declaration was found.

## WANTED

WANTED: ILO, Travaux de Gabber, Expose VIII Remark 3.1.29, printed p. 103, for the inherited motivation of lem-trf-finite-monoid-rational-coordinates. The PDF named by the item is absent from this read clone. It is not needed as a theorem for this proof; the algebraic proof here is explicitly agent-written from the available tensor universal property. No download or literature-list edit was made.

## Corrections and scope

The imported statement is correct and unchanged, including the tensor order G tensor Q and the empty cases. It had no proof. I retained its citations, blueprint ancestry, previous search records and creation metadata. The inherited ILO citation expressly says it motivates this algebraic statement rather than proving it; it is not being offered as an exact source. The actual proof source is the available Stacks algebra.tex, Tag 00CX (lemma-tensor-product and proof), with the bilinear relations of section-tensor-product, Tag 00CV. The proof_origin is agent, not document.

The current main-20261015 locality proof and its chapter and unit were read. This item is an algebraic descendant of its inherited normal-cone/log-geometry route, not the unit's key statement. The chapter, unit, route, and all other nodes are untouched. The blueprint searches for basis, rational cone and tensor coordinates gave no duplicate of the full item. Whole-DAG searches also checked tensor basis and scalar-extension statements; lem-sc-tensor-product-free-basis and def-weil-vector-space-scalar-extension do not state this group/rational-cone result. No node is created for a clause of the item, or for its elementary calculations.

Mathlib searches: actual Q83 LeanFinder and LeanSearch results concern number-field lattices or tensor definitions, not the conjunction here; the second LeanFinder phrasing concerns signed generator coefficients and returned tactics and a root-system result. Loogle TensorProduct, Module.Basis returns Module.Basis.baseChange and TensorProduct.equivFinsuppOfBasisLeft, which cover the basis portion. Read TensorProduct/Basis.lean:62-74 and 130-142; baseChange uses Q tensor G, whereas the statement uses G tensor Q. Read PointedCone.mem_hull_set, Pointed.lean:201-208, after the cone grep. Neither set of results proves the entire item in one specialization. The new proof avoids needing any identification with those APIs: it writes out the universal-property construction directly.

## Not duplicates

No new nodes, so no new/existing pairs require distinction.

## Review by Q83

I checked the item against its parent lem-trf-sharp-cone-lattice-intersection, especially step 3, where the coordinate maps give injectivity, the cone equality gives finite generation and the signed expression gives spanning. All these clauses are retained. I read the available source algebra.tex at lemma-tensor-product (Tag 00CX) and its explicit quotient construction. It states the universal property and, in the proof, that pure tensors generate. Both assertions also occur verbatim in def-weil-pbc-module-tensor-product's statement. I opened def-weil-module-base-change and verified that its statement gives exactly the scalar action a(m tensor b)=m tensor ab needed here. Both existing definition nodes have status mathlib. No new statement needs an independent source check.

Step 1 uses the tensor node's universal property, with R=Z, M=G, N=Q and target Q as a Z-module. Coordinate additivity and integer homogeneity are proved by uniqueness of the given integral expansion, so the map (g,q) to q lambda_k(g) really is Z-bilinear. No basis-extension theorem is assumed.

Step 2 cites the scalar-action formula from the base-change node and the pure-tensor generation clause from the tensor node. For each rational a, both maps being compared are Z-linear, agree on every g tensor q, and therefore agree on V. This explicitly proves Q-linearity, rather than treating the Z-linear universal property as a Q-linear one. The same check proves uniqueness.

Step 3 cites the same two nodes only for bilinearity, generation, and the scalar-action formula. The displayed pure-tensor expansion follows by substituting the given integral expansion of g and moving its integer coefficients across the tensor. The endomorphism E agrees with the identity on the stated generators. Applying L_h to a purported expansion gives d_h, since lambda_h(e_k) is the Kronecker delta by the hypothesis of unique integral coordinates. Reconstruction and uniqueness are proved in the step, not imported from a weaker node.

Step 4 uses only bilinearity and the scalar formula from the two cited nodes. It explicitly sets the new generator coefficient to the finite sum of q_l a_lj. Naturals are nonnegative rationals, so these coefficients are nonnegative. The reverse inclusion uses the coefficient vector with one 1 and all other entries 0. No saturation, sharpness, injectivity, or cone-hull theorem is used or needed.

Step 5 checks that the integer matrix expresses each basis vector in the actual group G, then uses additivity of i from the same two nodes. The finite-sum interchange is displayed, and the rational identity c=max(c,0)-max(-c,0) is checked in its two sign cases. The group-generation hypothesis supplies a row of the matrix for each basis vector; no monoid-generation hypothesis stronger than the definition of P is substituted.

Step 6 uses only the tensor node's generation clause. If m=0, the given group-generation condition forces G=0, and then all pure tensors vanish. If r=0, the integral expansion and the proven rational expansion are empty and force G=V=0. For r=0 with m>0 the generators and all signed coefficients are zero. I also tested G=Z, basis 1, generator -1 and matrix (-1): the coefficient of x is -x, and the asserted difference has the correct sign. Redundant zero generators cause no difficulty, and the cone proof allows an empty outer expression and zero coefficients. No hypothesis on saturation, a monoid injection or a field extension of Z is assumed.

Against delivery-errors B–E: there are no new statements, no hidden restatement leaf, and no reference to a cited node's proof as its interface. Each dependency is an existing Mathlib leaf and each has been opened and quoted from its statement. All six steps are direct calculations with definitions or the explicitly cited universal property and generation clause. Each step is shorter than 2000 characters. The long-step extraction rule therefore requires no further node. The citations file was checked by literal substring assertions. No statement dispute or unfinished mathematics remains; server preflight and final delivery results follow below.

## Validation

The required deliver.py --no-push completed successfully: OK (not pushed), server preflight passed, receipt commit 3c26a923396. No diagnostics required mathematical or structural repairs. This report addition is included in the final delivery.
