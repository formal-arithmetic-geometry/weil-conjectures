## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-frame-product-laurent-algebra.json` (item, statement, split; no Mathlib match), `citations.json`, and this report. The search command also wrote `searches.jsonl`. There are **0 new nodes and 0 new Mathlib leaves**.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag, frame-bundle terminology, simultaneous frames, and Laurent/frame combinations found no declaration stating the item. Generic module-sheafification code is already attached to its own existing node and is cited rather than attached to this item.

WANTED: none. The Stacks sources needed for the proof are present.

The imported node was statement-only, with no proof or proof dependencies. Its statement is correct, including the minus sign on tensor exponents; I preserved it verbatim and retained its source, provenance, and all five inherited Mathlib search records. Its blueprint ancestry already terminates in a null ancestor; `tools/blueprint_refs.py ancestor lem-sfb-frame-product-laurent-algebra` reports None. This delivery retains that provenance, including its detailed nonempty `from.place` and `via`, instead of inventing a blueprint identity. No statement dispute or source correction is needed.

Nothing mathematical remains unfinished at this split level. Downstream proving and the independent maintainer review remain outside this worker's scope.

## Proof and sources

I read Stacks `constructions.tex`, Tag 01M2, label `definition-vector-bundle`, and Tag 01LX, label `lemma-spec-properties`, including (1) and (3). They explain the relative-Spec vector-bundle algebra and its pushforward; neither states this Laurent frame-product assertion verbatim. Accordingly the proof is explicitly agent-written. I also read `schemes.tex` Tag 01I1, label `lemma-morphism-into-affine`; `categories.tex` Tag 001P, label `lemma-yoneda`; `morphisms.tex` Tag 01S8, label `lemma-characterize-affine`; and `sheaves.tex` Tag 009U, label `lemma-restrict-basis-equivalence-modules`. The algebra uses only finite sums; the infinite sum is sheafified, as the statement requires.

The current blueprint source read was `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This records the higher direct-image route; our node is an auxiliary Laurent calculation beneath the inherited torsor-section-extraction prerequisite. I read the chapter and unit records. No chapter or unit route was replaced.

## Searches and reuse

Before writing, I searched the whole DAG for 01LX, 01M2, Laurent algebras, affine-local-target, relative Spec, direct sums of modules, affine-basis sheafification, and morphisms into affine schemes. Whole-blueprint searches through `tools/blueprint_refs.py search` used `Laurent`, `relative Spec`, `frame`, and `sheafification`. No blueprint node states the item. Relevant existing nodes were opened, and their actual statements were compared to each application. In particular the field-only Laurent-ring definition was not used for arbitrary coefficient rings, the finite-rank tilde-free-module node was not used for the infinite direct sum, and the binary quasi-coherent direct-sum node was not used for an infinite sum. The torsor-frame-geometry node needs a field and a torsor; it was not used for an arbitrary scheme with a given representing object.

Fresh searches ran through the required `msearch.py Q59 lem-sfb-frame-product-laurent-algebra` command, not through a private service client:

- LeanFinder: `The algebra of functions on the product of line bundle frame schemes is the direct sum of integer tensor powers of the dual line bundles`. The eight hits include `TensorPower.galgebra`, `AlgebraicGeometry.ΓRestrictAlgebra`, and Proj structure sheaves. Their returned types have neither frame functors nor the Laurent pushforward comparison.
- LeanSearch: `Laurent algebra of functions on a line bundle with the zero section removed`. Hits give `LaurentPolynomial`, its polynomial localization and algebra, and Laurent series, without the scheme/frame/sheaf conclusion.
- Loogle: `AlgebraicGeometry.Scheme, LaurentPolynomial`: zero hits.
- grep: `frameBundle|frame_bundle|Laurent|integer.*tensor` in `AlgebraicGeometry`: zero hits.
- Second LeanFinder phrasing: `Pushforward structure sheaf of a punctured line bundle is the Laurent tensor algebra of the dual line module`. The hits concern generic Spec structure-sheaf stalks and `ModuleCat.tilde`; their returned signatures do not state the item.

All services answered. The exact queries and actual returned records are appended to the item and retained in `searches.jsonl`; the earlier Q111 records are preserved as inherited history. There are no new nodes for which a separate search or duplicate comparison is needed.

## Not duplicates

No new nodes. The existing basis-sheafification lemma, affine functor-of-points lemma, Yoneda lemma, and affine-local-target lemma are reused directly. The coordinate universal-property argument and transition computation are elementary proof steps, not new nodes restating clauses of the item.

## Review by Q59

I checked B–E of `coord/delivery-errors.md` with the node and sources open. No new statement-only obligations are introduced. The unchanged item introduces S, r, all line modules, the representing object and its tautological frames, the sheafified direct sum, and all exponent conventions. It cites the definitions it needs. Single TeX escapes are used in the decoded strings; the JSON is written with indent 1 and a final newline. Sources identify actual Stacks tags and labels, not changing section numbers. No SGA source is used.

Step 1 is the elementary Laurent-ring construction needed over **any** commutative ring. The proof writes finite-support convolution and the evaluation formula and proves uniqueness by the generators and their inverses. It does not import the field-only Laurent polynomial definition. This is neither an uncited localization theorem nor a moved clause of the item: it is a few-line explicit algebra calculation in the proof.

For step 2 I opened every cited node. `def-sc-invertible-module` actually says Zariski locally free of rank one; together with finite r it supplies a common trivializing neighbourhood. `lem-weil-pbc-affine-opens-basis` actually supplies an affine refinement of that neighbourhood, without any quasi-separatedness hypothesis. `def-pc-module-pullback` gives tensor inverse image and functoriality, so the chosen frames pull back. `lem-weil-pbc-morphism-into-affine-scheme` gives maps from an arbitrary scheme U into Spec C from maps C to global functions, not just affine U. Restricting to R-algebra maps enforces being over V. `lem-pc-yoneda` states the full Hom(h_X,F)=F(X) bijection, not only full faithfulness; applying it to the inverse natural transformations produces inverse morphisms. Invertibility of a frame is precisely invertibility of its scalar function, even over nonreduced rings. The universal frame and its coordinate are tracked at the identity test point.

For step 3 I read `pqf-lem-affine-local-target`: its third characterization is **existence** of an affine open cover with affine inverse images. That is exactly what step 2 provides. The distinction from the definition requiring every affine inverse image is essential; I explicitly cite the locality theorem rather than asserting this implication from the definition.

For step 4 I reread `def-pur-sheaf-tensor-product` and `def-sc-invertible-module` for the tensor powers, duals, and evaluation. The basis vector b_n multiplies with b_m to b_(n+m), so no tensor-coherence theorem is used without a calculation. `def-weil-affine-spectrum` states that global functions on Spec C are C. Step 2 applies on every affine W inside V, hence the module presheaf direct sum agrees with q_*O on that entire affine basis, including its restriction maps. `lem-sc-module-sheafification-affine-restriction` states exactly that such agreement implies an isomorphism after module sheafification. Its optional functor parameter is specialized to the terminal category. The resulting isomorphism is the extension of the basis maps; the algebra identities can be checked on their locally represented finite sums. I do not claim arbitrary open sections have globally finite Laurent support. This lemma is a generic off-unit tool, declared in `split_report.tool_uses`; the unit route contains no alternative basis-sheafification input.

Step 5 uses the actual dual, pullback and tensor definitions cited there. I recomputed the overlap law: e'_i=g_i e_i implies z'_i=g_i^(-1)z_i, while b'_n=(product g_i^(-n_i))b_n, so both maps agree. Evaluation of e_i^dual on tau_i gives z_i, whereas inverse-frame evaluation of e_i gives z_i^(-1). This verifies both positive and negative exponents and the normalization, rather than invoking an unnamed character convention. Maps and their inverses glue by the sheaf axiom; equality of restrictions and algebra identities are local. This is elementary once step 4 is in hand.

I tested r=0 (one degree and P=S), n=0 (the unit and structural scalar map), n_i=1 and -1 (the two evaluation directions), the empty scheme and zero ring, and coefficients R=k[epsilon]/(epsilon^2). Laurent coefficients remain unique because they are finite coefficient families, not rational functions in a domain. A nontrivial change of frame by a unit gives the same degree map as above. An infinite disjoint union of affine components requires no finite cover: all gluing is sheaf-local, so locally finite support is handled by sheafification. No separatedness, quasi-compactness, quasi-separatedness, reducedness, Noetherianity, or field hypothesis entered any application.

The main repairs relative to the empty imported proof are explicit use of the all-schemes affine functor of points, the locality theorem for affineness, the affine-basis sheafification theorem for the infinite direct sum, and the sign computation. Every cited statement has a verbatim quote in `citations.json`; I checked each quote against its source node, rather than substituting a claim found only in the node's proof. Every non-elementary step cites the relevant theorem. All five steps are below 2000 characters, and none hides a separate non-elementary comparison. No new dependencies are introduced back from a cited node to the item.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q59/lem-sfb-frame-product-laurent-algebra at 3f3b311c4c9: preflight passed`. This includes the maintainer preflight, DAG check and split review. After recording that result, the final report is checked again before pushing. No Lean file was written, no compiler or Lake tool was run, and no git command was run in the read-only shared repository.
