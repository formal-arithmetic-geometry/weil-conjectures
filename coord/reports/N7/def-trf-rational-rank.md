# Worker report: def-trf-rational-rank

## Files written

- `dag/nodes/sec-trace-formula/def-trf-rational-rank.json`: definition, split; no new nodes. Repaired the returned statement by making the dimension cardinal-valued for an arbitrary abelian group, explicitly giving the canonical \\(\\mathbf Q\\)-vector-space structure on \\(G\\otimes_{\\mathbf Z}\\mathbf Q\\), and removing the incompatible finite-dimensional dependency. The existing field and tensor-product dependencies remain.
- `citations.json`: empty, because a definition has no proof steps.

## Attachments

None. I searched both source checkouts under `WeilConjectures/` for `def-trf-rational-rank`, `rrk`, and rational-rank wording; no finished declaration states this definition without `sorry`.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, §2.1 notation immediately before Lemma 2.1.2 (the notation defining \\(E_{l/k}=\\dim_{\\mathbf Q}((|l^\\times|/|k^\\times|)\\otimes_{\\mathbf Z}\\mathbf Q)\\)); the local archival copy is absent. The source URL retained in the node is the only available copy.

## What was wrong or incomplete

The returned node quantified over an arbitrary abelian group \\(G\\) but cited `def-weil-vector-space-dimension`, whose statement assumes a finite-dimensional vector space and returns a nonnegative integer. This is not valid for general \\(G\\): for example, \\(G=\\bigoplus_{n\\in\\mathbf N}\\mathbf Z\\) gives \\(G\\otimes\\mathbf Q\\cong\\bigoplus_{n\\in\\mathbf N}\\mathbf Q\\), which has infinite dimension. I repaired the definition rather than adding an unstated finite-dimensional hypothesis: \\(\\operatorname{rrk}(G)\\) is now the cardinality of a Hamel basis of the canonical \\(\\mathbf Q\\)-vector space \\(G\\otimes_{\\mathbf Z}\\mathbf Q\\), possibly infinite. This is the general notion represented in Mathlib by `Module.rank`. The finite-dimensional dependency was removed; `def-weil-field` and `def-weil-pbc-module-tensor-product` still state the field and tensor constructions used by the formula.

## Review by N7

I read the complete returned item, `sec-trace-formula` and `sk-i-curve-zero`, the current main-20261015 blueprint branch for `lem-trf-local-term-locality`, and the full statements of `def-weil-field`, `def-weil-pbc-module-tensor-product`, and the removed `def-weil-vector-space-dimension`. The Temkin PDF is unavailable locally, so the cited §2.1 notation remains a WANTED source; the blueprint sentence supplies the same value-group-quotient formula. The item statement now agrees with that notation while making explicit the unrestricted cardinal-valued interpretation needed by its generic abelian-group wording.

There are no proof steps or step citations for this definition, so `citations.json` is correctly empty. The statement dependencies were checked clause by clause: `def-weil-field` supplies \\(\\mathbf Q\\) as a field, and `def-weil-pbc-module-tensor-product` supplies \\(G\\otimes_{\\mathbf Z}\\mathbf Q\\); the canonical scalar action and Hamel-basis cardinality are stated inline. The old finite-dimensional node was read and deliberately removed because its hypothesis and codomain do not apply here. I searched the whole DAG and blueprint for an existing rational-rank node or a more general cardinal-dimension definition, and searched both source checkouts for a finished declaration; none gives this project definition. Mathlib searches were rerun and logged for cardinal dimension, `Module.rank`, tensor products, and rational rank; `Module.rank` is the relevant generalization, while no named rational-rank definition exists.

I tested the repaired statement on \\(G=0\\) (rank 0), \\(G=\\mathbf Z\\) (rank 1), a finite torsion group \\(\\mathbf Z/n\\mathbf Z\\) (rank 0), and \\(G=\\bigoplus_{n\\in\\mathbf N}\\mathbf Z\\) (countably infinite rank). These cases expose exactly why a finite-dimensional dependency cannot remain. No new node was created, no proof was moved into a clause node, and no statement hypothesis was added or dropped.
