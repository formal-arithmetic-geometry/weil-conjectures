# Stage-1 worker report: lem-sfb-derivation-cohomology-scalar-square

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-derivation-cohomology-scalar-square.json`: statement, split; nine proof steps; Mathlib verdict: no exact project or Mathlib attachment. The mathematical statement is unchanged.
- `citations.json`: 17 step/node pairs, each with a verbatim excerpt of the statement actually used.
- `searches.jsonl`: the required search command's unmodified log. The item retains its inherited searches and adds the searches run by Q33.
- `report.md`: this report and the direct-delivery review. `prepare.py` is a sandbox-only preparation script, not a delivery file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, Hodge/Dolbeault terminology, derivations and differential cohomology found no declaration giving all clauses of the item. Ring-level differential formulas do not attach this cohomological statement.

## WANTED

None. All source material used is available in the read repository.

## Findings and changes

The item had no proof. The mathematical statement is correct, including in positive characteristic and for an arbitrary extension field. The derivation is only ground-field linear, so naturality restricted to O-linear maps would not prove its square. The split uses the existing **additive** edge-map compatibility node, rather than treating the derivation as a module morphism. It constructs each coefficient scalar comparison using module base change, and then calculates the square in complexes of ground-field vector spaces.

The proof of Stacks Tag 02KH (`coherent.tex`, label `lemma-flat-base-change-cohomology`) supplies the separated affine-cover route. I also read Tag 02KG (`lemma-affine-base-change`), Tag 01XD (`lemma-cech-cohomology-quasi-coherent`) and the affine-diagonal calculation immediately preceding it. The module/abelian comparison is Tag 01F1 (`cohomology.tex`, `lemma-modules-abelian`) and its site version Tag 03FD (`sites-cohomology.tex`, `lemma-cohomology-modules-abelian-agree`). The additive Cech comparison comes from Tags 03AX and 03F7 in `sites-cohomology.tex`; their actual statement and double-complex/degeneration arguments were read. Tag 00RV (`algebra.tex`, `lemma-differentials-base-change`) explicitly constructs the derivation by $d(\sum a_i\otimes\lambda_i)=\sum da_i\otimes\lambda_i$. Its ring-level node supplies precisely the base-change isomorphism and generator formula used here.

The combination into a scalar square is marked `proof_origin.by = agent`; it is not falsely attributed as a verbatim proof of 02KH. I corrected the source metadata to name actual tags and labels instead of relying on another item's report. Two statement dependencies were added for the already present fibre-product and small Zariski-site notions; no hypothesis or conclusion changed.

I read the chapter and unit records and the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof, especially paragraph (3). This item is a supporting input to the inherited Kodaira/Hodge branch. The chapter and unit route are unchanged. `blueprint_refs.py ancestor` currently reports `None` for this pre-existing long creation chain; I retained its existing ancestor/via data and made its place more precise with the latest blueprint path. The server's `review_split` accepted this field. Whole-blueprint searches for `cohomology scalar`, `derivation`, `01F1` and `03FD` found no node stating this entire scalar square; `same_as` remains empty.

## Mathlib searches and existing-node reuse

LeanFinder was queried with the cohomology/base-change statement and with the alternative Cech phrasing; LeanSearch, Loogle and Mathlib grep were also run through the mandated `msearch.py`. All services answered. Their queries are copied exactly into `mathlib_searches`. Semantic hits concerned ring-level cotangent maps and universal derivations, not cohomology of Zariski sheaves. I read `KaehlerDifferential.map_compDer` and `map_D` at `Mathlib/RingTheory/Kaehler/Basic.lean:662,668`, and inspected the cotangent-map source in `RingTheory/Extension/Cotangent/Basic.lean`. These are not the required sheaf-cohomology comparison. A broad grep also found irrelevant occurrences of `map_div` and determinant formulas; the subsequent precise grep isolated the differential formulas. No search outage has been recorded as absence.

Before contemplating any new node, I searched the whole DAG by 02KH/01F1 and by the cohomology-forgetting, affine-intersection, Cech-naturality and differential-base-change notions. Reading the statements showed that every substantive ingredient already has a node. In particular, `lem-sc-cech-comparison-map-naturality` only covers O-linear maps and was deliberately not used to justify the derivation's naturality. `lem-weil-pbc-module-abelian-derived-direct-image-comparison` concerns the etale site and was not substituted for the required Zariski comparison. `lem-pc-flat-tensor-complex-cohom` has a bounded-complex hypothesis; it was not applied to the unbounded full Cech complex. Instead, the existing exact scalar-extension leaf is used directly on the kernel, image and quotient in a fixed degree.

## Not duplicates

No new nodes were created. Existing general statements are cited; no clause of the item was moved into another node.

## Review by Q33

I reviewed the actual node statements and source passages above against delivery-errors B through E. There is one changed item and no statement-only node to check for missing objects, illicit proof sketches, duplicate tags, or invented Mathlib matches. The item's statement is retained, all proof dependencies are the union of step citations, all cited ids were opened and are unmerged, and all steps are under 1000 characters. No long-step lemma is hidden by prose.

Step 1 uses `lem-sfb-ringed-site-global-module-abelian-cohomology`. Its statement applies to **any** commutative ring sheaf on a small site and gives a canonical additive comparison natural in the module. Therefore it applies both to O_X and to the constant k ring sheaf on the same Zariski site. The comparison is linear because scalar multiplication is an endomorphism in each category; this is not a claim that forgetting preserves injectives. Replacing k by K proves the other comparison. The elementary identification of vector-space sheaves with modules over the constant ring sheaf is explained by gluing the constant local scalar actions.

Step 2 uses `lem-pc-projective-proper`, the definition `def-weil-proper-morphism`, `lem-weil-pbc-qcqs-finite-affine-open-cover`, `lem-weil-pbc-separated-affine-open-intersection`, and `lem-pc-finite-affine-cech-intersection-base-change`. The first states projective implies proper without a dimension restriction; properness explicitly includes separatedness. Quasi-compactness is part of the given projectivity convention, so the finite-cover lemma applies. The affine-intersection leaf assumes a separated morphism to an affine base, exactly X to Spec k. Iterating it gives every tuple intersection. The last cited statement makes the pulled-back intersection affine over Spec K, which is affine, so its underlying scheme is affine. No intersection of arbitrary opens on a merely quasi-separated scheme is asserted affine.

Step 3 uses the affine-local definition `pqf-def-coherent`, the full statement of `lem-weil-pbc-kahler-differentials-base-change`, and the universal derivation definition. The item itself constructs the differential sheaf by gluing the associated affine modules; this gives quasi-coherence directly, and does not require smoothness or finite rank. The cited differential node includes both invertibility and the generator formula, as well as linearity over A tensor K. Tensor reassociation gives the module pullback form. Restriction compatibility is written on generators b da, so it is an elementary gluing of these existing isomorphisms, not an uncited sheaf base-change theorem. The p=0 comparison is the defining tensor identity for pullback of the structure module.

Step 4 uses `pqf-lem-affine-vanishing`, the general ringed-site scalar-forgetting comparison, and `lem-weil-pbc-acyclic-cech-edge-compatibility`. The first applies to each affine tuple intersection and the quasi-coherent coefficient sheaves of step 3. Applying the second on the open intersection transfers the vanishing to abelian and vector-space cohomology. The third explicitly supplies the canonical edge isomorphisms, their naturality for **every additive sheaf map**, and their compatibility with module forgetting. This is exactly the stronger statement the step needs. The scalar actions and the non-O-linear derivations therefore give the claimed edge identities. The derivation cochain maps commute with the alternating restriction differential by the written coordinate calculation, not by an O-linear naturality assertion.

Step 5 uses `lem-pc-flat-cech-base-change`. Its statement gives a chain isomorphism with precisely the pullback-unit coordinate formula for a separated morphism, finite affine family and quasi-coherent module. Those hypotheses hold by steps 2 and 3; this node does not need flatness or finite-dimensional cohomology. The symmetry of tensor factors is explicit. The comparison is used separately on F_0 and F_1; no invalid use of module functoriality on d is made.

Step 6 cites the universal derivation definition and the ring base-change node for the only formulas it takes from them. Both paths on a tensor with coordinate a are written out: the Leibniz term involving d(lambda) is zero because lambda is a ground-field scalar for the K-derivation. This proves equality on pure tensors, and hence on all elements. It uses no characteristic-zero, connectedness or integrality assumption. This two-line calculation from the cited formulas belongs in the proof rather than in a new node.

Step 7 uses the Mathlib leaf `lem-weil-field-scalar-extension-exact`, whose statement gives additivity and exactness for every field extension. Exactness preserves the cycle kernel, boundary image and their quotient, so the homology comparison is invertible in any fixed degree. Its naturality is checked on a cycle class tensor lambda; there is no bounded-complex assumption or illicit passage through an infinite product.

Step 8 again uses the **site-change** clause of `lem-weil-pbc-acyclic-cech-edge-compatibility`. Inverse image on opens preserves the final object, all intersection products and covering unions. The coefficient map is h_p, and its components are exactly those used by theta on tensors with scalar 1. The source and target acyclicity were proved in step 4. Thus the statement actually gives the claimed cohomology-pullback normalization; after K-linear extension it characterizes beta independently of the cover. The same node's forgetting clause justifies its agreement with the module comparison. This avoids choosing unrelated Leray isomorphisms for the two coefficients.

Step 9 uses only the identities already proved in steps 4, 6 and 7, and substitutes them into the composite defining beta. I checked the directions and tensor factors and included the value on a cycle representative. It is therefore elementary assembly, not a new assertion of functoriality.

I tested the proof on X empty (one may take a single empty affine open, all section vector spaces are zero), q=0 (there is no boundary from negative degree), K=k (the coefficient maps become identities), disconnected X, and arbitrary large q (no boundedness assumption enters). I also checked an inseparable extension in positive characteristic: the differential is relative to k on X and relative to K on X_K, so d(lambda)=0 remains valid. The example k[t] and d(t)=dt verifies that no mistaken O-linearity was used. Finite products occur in each Cech degree because the affine cover is finite, even though there are arbitrarily high degrees; no commutation of tensor with infinite products is assumed. Smoothness is not needed by this scalar argument but remains a hypothesis of the unchanged item.

The off-unit cohomological and geometric statements are declared in `split_report.tool_uses`: generic tools for this calculation, not replacements of the unit's route. No maintainer-owned `tool_uses` field, unit record, Lean file or source file was modified. No SGA source was used. The pre-report server `review_split` passed with zero new nodes. Direct delivery follows the user brief: there is no second worker review represented here.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler, Lake or build command was run. Full delivery dry-run and push are performed after this report is written.
