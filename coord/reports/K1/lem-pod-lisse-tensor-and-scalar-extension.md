1. Files written:

- `dag/nodes/sec-poincare-duality/lem-pod-lisse-tensor-and-scalar-extension.json` — statement, split proof, Mathlib searches recorded.
- `dag/nodes/sec-poincare-duality/lem-pod-etale-stalk-tensor-scalar.json` — statement-only supporting node, no Mathlib match.
- `citations.json` — verbatim citations for every non-elementary step.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof and had only two grep searches. I retained its mathematical statement, added the missing blueprint location and same-as search result, and supplied the proof steps. The stalk formulas are not elementary consequences of the lisse definition, so they are isolated in the generic supporting node rather than silently treated as local calculations. The existing node `lem-weil-pbc-constant-sheaf-geometric-stalk` was reused for the constant-sheaf clause.

5. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` with this item tag or statement. Mathlib searches returned only unrelated affine or topological stalk declarations; LeanSearch was unavailable and is recorded as such.

## Not duplicates

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-constant-sheaf-geometric-stalk`: the new node treats tensor products and scalar extension of arbitrary sheaves on the etale site, while the existing node treats only the stalk of one constant sheaf.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-pc-ringed-space-module-stalk-tensor`: the existing node is for sheaves of modules on a topological ringed space; the new node is for geometric stalks on a scheme's small etale site and also includes scalar extension.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-pod-lisse-tensor-and-scalar-extension`: the supporting node is a generic stalk theorem for arbitrary etale sheaves; the item additionally assumes lissity and proves local constancy, finite coefficients, and coherence clauses.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-stalk-change-of-rings-tensor`: the existing node is a topological-space change-of-rings statement; the new node is geometric stalks on the small etale site and includes tensor products and composite-extension coherence.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-filtered-colimit-tensor-varying-rings`: the existing node is an algebraic filtered-colimit tensor lemma; the new node is its sheaf-theoretic etale-stalk consequence.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-module-stalk-pullback`: the existing node concerns pullback of module sheaves; the new node concerns tensor products and coefficient extension at geometric etale stalks.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-module-stalk-tensor`: the existing node treats topological or scheme module stalk tensors; the new node treats geometric etale stalks and also scalar extension.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-pur-isomorphism-inverse-image-tensor-hom`: the existing node is an inverse-image tensor-Hom isomorphism; the new node is a stalk comparison for lisse etale sheaves.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-sheafification-geometric-stalk`: the existing node gives sheafification invariance of geometric stalks; the new node applies this to tensor and scalar-extension presheaves and states their resulting isomorphisms.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-weil-pbc-sets-sheafification-geometric-stalk`: the existing node is set-valued sheafification and stalk invariance; the new node is module-valued tensor and scalar extension.

`lem-pod-etale-stalk-tensor-scalar` vs `lem-galois-stalk-representable`: the existing node identifies a stalk of a representable finite etale sheaf; the new node identifies stalks of tensor and scalar-extension constructions.

## Review by K1

I read the imported item and its parent `cor-galois-lisse-representations`, including the parent paragraphs “Tensor products” and “Base change of coefficients”. I checked the source references Stacks Lemma 093V (local constancy of tensor products), etale-cohomology Lemma 095D, sites-modules Lemmas 03EL and 008B, and etale-cohomology Lemma 04FM. The statement keeps the finite-ring hypotheses, the geometric stalk, the sheafification convention, all germ formulas, naturality, and coherence clauses.

Step 1 uses `lem-weil-pbc-constant-sheaf-geometric-stalk`; that node explicitly gives the constant-sheaf stalk isomorphism, and the module-linearity check is the scalar/additive compatibility of the germ map. Step 2 uses only the etale-site and sheafification definitions: a common trivializing etale cover makes both constructions constant, and finiteness is immediate for finite modules. Step 3 uses the supporting node, whose statement is exactly the tensor stalk isomorphism and its naturality/coherence. Step 4 is the pure-tensor associativity calculation for successive coefficient extensions. Step 5 uses the supporting node's second displayed isomorphism, including its precise germ formula and module structure. Each citation in `citations.json` is copied from the cited node's statement.

I searched the whole DAG and blueprint for tensor/stalk/scalar-extension duplicates before creating the supporting node. The only close existing results were the constant-sheaf stalk lemma and a topological ringed-space tensor-stalk lemma; their hypotheses and conclusions differ as described above. I tested the constructions on the trivial sheaf and on a one-point etale site: the formulas reduce to the ordinary module tensor and scalar-extension identities. No source or Lean declaration supplied the generic etale stalk formulas, so the supporting node remains unsplit for the next stage.

## Second reading by K1

- Item statement: compared verbatim with the imported theorem and its source places 093V, 095D, 03EL, 04FM, and 03PN; the three clauses and all hypotheses are retained.
- Step 1: checked against `lem-weil-pbc-constant-sheaf-geometric-stalk`; its statement supplies the stalk isomorphism, while module linearity is definitional.
- Step 2: checked the common etale trivialization argument against the lisse definition, sheafification definition, and 093V/095D; the local tensor and scalar-extension calculations are elementary.
- Step 3: checked against the full statement of `lem-pod-etale-stalk-tensor-scalar`; it supplies the tensor stalk map, naturality, and coherence.
- Step 4: checked the pure-tensor associativity calculation for successive scalar extensions; this is elementary and does not require a new node.
- Step 5: checked against the scalar-extension clause of `lem-pod-etale-stalk-tensor-scalar`; it supplies the germ formula, module linearity, naturality, and composite compatibility.
- `lem-pod-etale-stalk-tensor-scalar`: checked as a self-contained statement with scheme, etale site, geometric point, module-sheaf, tensor, and sheafification notions cited; tested on the zero module, a field, and a one-point etale site. It is strictly smaller than the item and is not a duplicate of the constant-sheaf or topological stalk nodes.

Changes made: restored the exact imported item statement and source (the worker summary had replaced it with a weaker paraphrase), restored the imported blueprint location, removed the unsupported sheafification statement dependency from the item metadata, and added the required second-reading record. The repository's maintainer-owned `created` metadata remains unchanged and is corrected by delivery packaging.
