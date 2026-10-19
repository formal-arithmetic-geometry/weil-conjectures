Files written:

- `dag/nodes/sec-trace-formula/def-trf-mittag-leffler-module.json` — definition; no new Mathlib leaf.

Attachments:

- No attachment: grep of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` found no declaration tagged `(blueprint: def-trf-mittag-leffler-module)` or an equivalent sorry-free project declaration.

WANTED:

- None. The source definition and its tensor criterion are available in `literature/stacks-project/algebra.tex`.

What was checked and changed:

- The item statement was checked against Stacks, Tag 059F (`definition-mittag-leffler-module`) and the equivalent tensor-product criterion in Tag 059M, Proposition `proposition-ML-tensor`, condition (2). The statement introduces a commutative ring, module, arbitrary family of modules, and the canonical tensor-to-product map, and agrees with that criterion.
- The existing dependency `def-weil-pbc-module-tensor-product` was opened and verified to state the tensor-product universal property used by the definition. No additional node is needed: products of modules and the displayed componentwise map are part of the definition's construction and do not require a separate theorem node.
- The whole DAG and blueprint were searched for duplicates and for a blueprint node stating this definition. No duplicate or alternate statement was found. The item blueprint ancestry was filled from `lem-trf-local-term-locality`, at the sentence fixing the Mittag-Leffler tensor criterion.
- The source declaration search found no finished project Lean declaration. The item is therefore marked `split`; as a definition it has no proof steps, so `proof`, `proof_deps`, and `citations.json` are empty.
- Mathlib searches were run with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch. The hits (`TensorProduct.piRightHom`, `Functor.IsMittagLeffler`, and tensor injectivity lemmas) do not state the module-level Mittag-Leffler predicate; all were recorded as no match in the node's existing search log.

## Review by Q44

I read Stacks `algebra.tex` at Tags 059F and 059M and compared the complete item statement clause by clause: the quantification over every set and family of modules, the canonical map from the tensor product with the product to the product of tensor products, and injectivity all match the cited tensor criterion. I also read the existing tensor-product dependency, which supplies the tensor object and its universal property. There are no proof steps for this definition, hence no cited step statements or hypotheses to audit and no citation entries. I searched the DAG and blueprint for duplicate definitions and checked the upstream Lean source trees for an exact, sorry-free declaration; neither produced an attachment. I tested the edge cases conceptually: an empty family gives the map to the terminal zero product, a singleton family gives the canonical identity-style tensor map, and a zero module satisfies injectivity trivially. The only correction was changing the item status from `unsplit` to `split` and recording the blueprint location and review; no statement or dependency text was changed.
