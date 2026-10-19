# Q99 stage-1 report: lem-sf-cbc-extension-zero-completion

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-cbc-extension-zero-completion.json`: item split into seven proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None. A search of the slopmaster2 source found no sorry-free declaration tagged `(blueprint: lem-sf-cbc-extension-zero-completion)` and no declaration stating the item exactly.

## WANTED

None.

## What was wrong or incomplete

The imported item had an empty proof, empty proof dependencies, no proof origin, and an unspecified blueprint proof location. Its statement was retained. The split fills the strict K-flat tensor calculation, strict quotient-tower compatibility, completion-unit reduction isomorphism, normalized definition of `q_{j,K}`, completion presentation, witness transport, and naturality. The existing node `lemma-weil-pbc-adic-completion-reduction` is used as a tool because it supplies the non-elementary finite-reduction assertion needed for the completion unit; this is declared in `split_report.tool_uses`.

I searched the DAG and blueprint for duplicate tensor, completion, strict-tower, and extension-by-zero assertions before deciding that no new node was needed. Every new proof step is below 2000 characters and was checked for hidden sublemmas. No statement was weakened and no ordinary extension-by-zero/inverse-limit commutation was introduced.

## Review by Q99

I read the item source in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/fix-lem-exchanges.md`, including the integral-open-factor paragraphs and the completion-unit paragraph, and compared each clause of the imported statement with the seven steps. I also read the current statements of every cited node.

Step 1 uses `lem-pc-kflat-resolution` for a flat-term K-flat representative, `lem-pur-site-restriction-module-adjunction-exact` for exact extension by zero, `lem-weil-pbc-ringed-slice-extension-tensor` for the tensor comparison, and `def-pc-kflat-complex` for the K-flat criterion. The hypotheses are the ringed localized sites and the constant coefficient sheaves in the item.

Step 2 uses `lem-weil-pbc-diagram-site-realization` to identify tower objects with diagram-site modules, the same tensor comparison, and `def-weil-inverse-system` for the transition-square condition. I checked that the pure-tensor formula commutes with every quotient map, so the comparison is an actual strict-tower map rather than only a family of evaluated isomorphisms.

Step 3 uses `lemma-weil-pbc-adic-completion-reduction`. Its statement explicitly assumes the Noetherian complete-coefficient datum, additive torsion modulo the ideal, and perfect quotients, and explicitly says no derived-completeness hypothesis on the input is needed. Together with `lem-sp-completed-pullback-adjunction`, this identifies the components of the reduced completion unit with the adjoints of the limit projections and proves their invertibility.

Step 4 checks the normalization equation defining `q_{j,K}` and its naturality using the same two completion statements. The inverse and forward level maps are exactly the two maps described by the finite-reduction lemma and the completion adjunction.

Step 5 uses `lem-cbc-proetale-extension-zero-comparison`, whose statement gives the natural étale/pro-étale extension-by-zero comparison for every finite quotient, and `def-weil-pbc-etale-origin-witness`, whose statement retains the witness pair. Applying the comparison to each witness produces the claimed extension-by-zero witnesses. The diagram-site node supplies compatibility with the strict transitions.

Step 6 uses the completion adjunction’s explicit formula `C_XM=R\lim_n(M\otimes^L P_n)` and the strict-tower derived-limit model `lem-weil-pbc-ringed-strict-tower-homotopy-limit`. Substitution of the strict tower from Step 2 gives the stated `R\lim(J_j\mathcal R_UK)` presentation. I checked that this argument never applies ordinary `J_j` to an inverse limit, matching the item’s final qualification.

Step 7 checks functoriality, identity/zero edge cases, and transition compatibility from exact extension and the natural transformation definition of inverse systems. The cases `j=id` and `K=0` reduce directly to the identity and zero maps.

The required Q99 Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; all returned no relevant Mathlib theorem. The server-side `check_dag` preflight passed.
