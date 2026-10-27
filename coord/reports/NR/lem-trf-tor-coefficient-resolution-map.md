# Worker report: lem-trf-tor-coefficient-resolution-map

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tor-coefficient-resolution-map.json`: statement item, now split into four steps; no exact Mathlib match for the entire coefficient-action/tensor-extension assertion.
- No new DAG nodes and no new Mathlib leaves. The proof reuses two existing Mathlib leaves and the existing coefficient-action statement.
- `citations.json`: ten verbatim quotations, one for every step/node pair.
- `searches.jsonl`: the search command's own records; `write_split.py` is sandbox-only preparation code.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint tag and for Tor coefficient/resolution language. `Algebra/TorOneSurjectiveChangeRings.lean` is about first Tor and a different change-of-rings map; `Algebra/TorDimensionShiftFree.lean` is dimension shifting. Neither states this item's all-degree identity. No project declaration proving the whole item was found. The node itself has no Lean attachment.

## WANTED

None. All mathematical sources used are available locally.

## What was wrong or needed completion

The live item was statement-only and the sandbox had no prior split. I preserved its statement, statement dependencies, provenance and inherited search history. Its source pointer to 00M8 concerns flat change of the base ring; this item's base ring remains R, and its coefficient map is defined without flatness. I read 00M8 but do not take its isomorphism assertion as a hypothesis or as a proof of the fixed-base identity. The accurate direct source for the identity is 00LY, following 00LZ (functoriality in the second variable), together with 00M7 item (1) for coefficient actions. The proof_origin and step sources state this distinction. No statement correction or STATEMENT-DISPUTED is needed.

The general resolution-naturality fact already exists as `lem-weil-pbc-tor-map-via-resolution-lift`, clause (2). It would be a duplicate to create a coefficient-naturality node here. The balancing and generator arguments are short proof steps, not new nodes. The inherited blueprint ancestor is `lem-trf-local-term-locality`; I read its current main-20261015 proof and the chapter/unit records, and kept this descendant's existing algebra-tool route through its immediate parent `lem-trf-tor-flat-base-change` repair step 4. The current ancestor does not itself state the algebra lemma. Nothing in the unit or chapter is edited, and no SGA source is used.

## Searches and reuse

I read the item and all six statement-dependency statements, then searched the DAG for Tor functoriality, comparison of resolutions, the source labels `lemma-tor-welldefined`/`lemma-compare-resolutions`, and declaration names. This found the existing Tor-map leaf, whose complete statement and Mathlib match I read. `blueprint_refs.py ancestor` confirms the inherited ancestor. Whole-blueprint searches for Tor and the more precise coefficient-map/natural-transformation phrases were used to check whether another imported statement gives the assertion. No additional same_as identification was found.

The required Mathlib searches were run with msearch.py and their exact tool/query/result records appended to mathlib_searches. The second phrasing returned `CategoryTheory.ProjectiveResolution.leftDerived_app_eq`; I read `Mathlib/CategoryTheory/Abelian/LeftDerived.lean` lines 215--251 and `CategoryTheory/Monoidal/Tor.lean` lines 38--55. Its specialization is already recorded in clause (2) of the Tor-map leaf; there is no new Mathlib node. In particular, the source derives Tor' in the first variable, as required for a resolution of M. The search hits for naturality in the resolved variable alone do not prove the coefficient clause. The lemma Projective.of_free was also checked in Algebra/Module/Projective.lean at lines 152--162.

## Not duplicates

No new nodes; there are no new/existing same-tag pairs to distinguish. Reused `lem-weil-pbc-tor-map-via-resolution-lift` rather than creating its coefficient-variable special case, and reused `lem-weil-pbc-free-module-projective` and `lem-trf-tor-resolution-coefficient-actions` unchanged.

## Review by NR

For the item I read algebra.tex at 18215--18290 (00LY and 00LZ), 18713--18757 (00M7 and 00M8), the tensor-product definition node with its 00CV/00CX source, and the chain-complex homology definition with its 010V source. There are no new nodes needing separate sources. I read the complete statements of every proof citation, not just their titles or proof text.

Step 1 uses the tensor universal property and the explicit definition of an induced homology map. The displayed formulas establish R-balancing, A-linearity, the chain identity, preservation of cycles and independence of representatives; no exactness of coefficient extension is asserted. The quoted tensor node gives the universal property and generation; the homology node explicitly gives the cycle/boundary quotient and induced map. The coefficient homomorphism g is R-linear because the specified R-to-B structure is the composite.

Step 2 uses exactly the free-implies-projective statement and clause (2) of the Tor-map leaf. Its hypotheses are verified: R is commutative, all P_j are free hence projective, the augmented sequence is exact by the item's hypothesis, n is nonnegative, and g is an R-linear coefficient map. The leaf's equality is the equality this step takes from it, with N=A and N'=B. The coefficient definition says the named canonical coefficient map is the functorial map of the underlying R-linear homomorphism, so this does not substitute an arbitrary map. It is a citation of a statement, not of a hidden construction inside its proof.

Step 3 uses the coefficient-action lemma for both iota linearities and the restriction of the B-action along g. Its hypotheses are exactly the current ring tower and free resolution. The coefficient definition gives A-linearity of the coefficient map (regard g as the map from the A-algebra A to B). These cited statements, followed by the written balancing equation, give both tensor extensions. The tensor node supplies existence/uniqueness for balanced bilinear maps, and the displayed generator formula gives B-linearity. There is no appeal to a flatness definition or to exactness of tensor products.

Step 4 uses the established identities and the tensor node's generation assertion to prove equality of B-linear maps. The explicit cycle formula uses the action-on-homology formula in the coefficient-action lemma, which its quotation contains verbatim. It does not merely say that some unspecified comparison transports the maps. The arbitrary-resolution quantifier comes from applying the Tor-map leaf to the supplied resolution in Step 2, so no extra independence theorem is silently assumed.

I checked delivery-errors B--E point by point: no statement-only child contains a proof because there are no children; notions have their existing definition nodes; all TeX has single mathematical backslashes after JSON decoding; no claim of an attachment is made; every non-elementary input is cited; no clause has been renamed into a child; the pure-tensor calculation supplies the assembly. Both non-elementary steps have citations and are under 700 characters, well below the long-step threshold. The two off-unit statements are existing Mathlib leaves, so they are tools under the route rules without a new tool-use declaration. The coefficient-action lemma is in the item's own unit. No dependency reaches upward through the item in the argument; the remote graph check remains the final cycle check.

Small cases checked: for n=0 the complex is unaugmented, d_0=0, so the proof still uses the usual H_0 quotient rather than falsely imposing augmentation-kernel cycles. For M=0, B=0, or the zero ring all displayed maps have the indicated zero values. For g=id the chain map is identity and the tensor extension is the usual scalar multiplication. For a genuinely nonflat example R=A=Z, M=Z/2, B=Z/2, n=1, the source of c_1 is zero while its target is Z/2: both sides of the asserted identity are zero, and no invertibility follows. Infinite bases cause no infinite sums because each tensor element is a finite sum of pure tensors. Boundaries map to boundaries by the actual chain equation in Step 1.

## Unfinished work

No mathematical part remains in this one-level split. The existing coefficient-action node remains a separate dependency; its proof is not silently supplied here. Delivery is subject to the required server dry run and push recorded below.
