# Stage 1 report: lem-weil-pbc-ideal-times-quasi-coherent-affine-sections

Split the node into four proof steps:

- affine reduction identifies the multiplication map with the module multiplication map on sections;
- the reviewed quasi-coherent image/cokernel node gives quasi-coherence, the affine product formula, and the quotient kernel formula;
- induction gives quasi-coherence and affine sections for every ideal power;
- the local-image description proves compatibility with restriction to every open.

The proof follows Schemes 01I8 and 01IC, Modules 01CE and 01AH, and the affine product calculation used in Cohomology of Schemes 087X. No new node was created; all dependencies are existing public DAG nodes.

Checks to be run by the lead on the current base: review_split.py, check_dag.py --cycles, and preflight_delivery.py.

## Review by E1

I checked the four steps against Schemes 01I8/01IC, Modules 01CE/01AH, and the affine product calculation in Cohomology 087X. The proof cites the existing affine tilde/tensor comparison and quasi-coherent image/cokernel nodes for the multiplication map, then uses that result inductively for ideal powers and the local image definition for restrictions. Every reusable result is an imported public DAG node; this item adds no private or new lemma. The item has `status: split`, matching proof dependencies, and a complete split report; no Lean file changes.
