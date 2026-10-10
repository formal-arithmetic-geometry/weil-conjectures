1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-ample-proj-open.json`: item split, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-ample-finite-affine-cover.json`: statement-only supporting node, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-ample-proj-local-chart.json`: statement-only supporting node, no Mathlib match.

2. Attachments: none.

3. WANTED: none; the Stacks source is available in the local review checkout and is cited directly.

4. The item was unsplit. I read Properties Proposition 01Q3 and Lemma 01Q1 in `properties.tex`, including the construction with the section ring $S=\\Gamma_*(X,\\mathcal L)$, the finite affine principal-open cover, the inverse-image identity for $D_+(s)$, and the localization isomorphism on each affine chart. I also read the existing definition node `def-weil-pbc-ample-invertible-module` and searched the DAG, blueprint index, source Lean, and Mathlib for an exact declaration or duplicate node. No exact Lean declaration exists; the source repository's ample theorem is a different relative very-ampleness notion.

## Review by F1

For step 1, I checked that `lem-sc-ample-finite-affine-cover` states exactly the finite family of positive tensor powers whose affine nonvanishing loci cover $X$, which is what the step takes from ampleness. For step 2, I checked that `lem-sc-ample-proj-local-chart` explicitly states both $f^{-1}(D_+(s))=X_s$ and the affine-chart isomorphism, so it supplies the claimed local identifications rather than merely defining the canonical map. Step 3 only glues restrictions of the same canonical morphism and is elementary. The two new nodes are statement-only as required; each introduces its objects and records the 01PS/01Q1 source, blueprint ancestor/place, and LeanSearch, LeanFinder, and Mathlib-source searches. I checked small cases mentally: for $X=\operatorname{Spec}(A)$ with $\mathcal L=\mathcal O_X$, the section ring gives the usual principal affine chart, and for $X=\mathbf P^1$ with $\mathcal O(1)$ the two standard charts glue to the standard open immersion into Proj. The item statement and hypotheses were left unchanged.

5. What I could not finish: no Lean proof was written because this is a stage-1 DAG delivery; the supporting nodes remain unsplit statement nodes for later work.

Repair note: the returned E2/B and C1 issues were corrected. I read Stacks 01PZ in addition to 01Q1: the local-chart node now assumes that positive-degree homogeneous nonvanishing opens cover X and asserts existence of the canonical morphism before stating its inverse-image and affine-chart properties. Step 1 now obtains the finite affine cover first, invokes that hypothesis, and only then uses the canonical morphism. Its citations.json entry quotes the finite-cover sentence and the local-chart existence sentence verbatim; step 2 quotes the revised inverse-image and isomorphism sentence.
