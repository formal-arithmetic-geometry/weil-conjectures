1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-module-opcycles-tor-surjection.json` — statement, split proof, no new nodes, Mathlib searches recorded.

2. Attachments: none.

3. WANTED: `literature/stacks-project/more-algebra.tex`, Lemma 15.59.2 (Tag 0653), for the source proof text; the checkout has only the imported citation, so the argument is written from the standard Tor resolution calculation.

4. No new nodes were needed. I searched the DAG for Tor long exact sequences, tensor right exactness, flat Tor vanishing, and opcycle homology; the generic Tor sequence and tensor right exactness nodes already exist. The project source has no declaration tagged `lem-pc-module-opcycles-tor-surjection` and no matching sorry-free declaration.

## Review by M1

I checked the item statement against the imported Tag 0653/0654 route and kept its hypotheses: a commutative ring, a cochain complex with flat terms, the degree-a cokernel, every module N, and a natural A-linear surjection. Step 1 uses the existing node `lem-weil-pbc-tor-long-exact-first-variable`, whose statement gives the exact low-degree Tor sequence for the short exact sequence `0 -> K -> P^a -> Q -> 0`; it uses `def-weil-pbc-flat-ring-map` for injectivity after tensoring and `def-weil-pbc-tor-modules` for Tor as resolution homology. Steps 2 and 3 use the exact rightness statement `lem-weil-pbc-tensor-right-exact` to lift elements through `P^{a-1} tensor N -> K tensor N`; the differential identities show precisely that cycles map to the kernel and that every kernel element lifts to a cycle. Step 4 uses the naturality explicitly stated in the Tor-sequence node and the functoriality in the Tor definition.

I verified the edge cases conceptually: if `P^{a-1}=0`, the asserted surjection reduces to the zero kernel and hence Tor vanishes; if `d^{a-1}=0`, then `K=0` and both the kernel and Tor target are zero. I corrected the imported empty proof by writing the kernel identification and lift argument instead of treating the Tor surjection as automatic. The two off-unit citations are declared as tool uses because they are generic module homological facts not supplied by the Picard-duality route. Mathlib searches were run for the item: LeanFinder returned flatness/exactness and Tor-projective declarations but no exact theorem, Loogle reported an unknown `Tor` identifier, grep found no matching declaration, and LeanSearch was unavailable.

## Second reading by M1

- Item statement: checked against More on Algebra, Tag 0653 (`lemma-last-one-flat`) and the imported Tag 0654 route; the ring/module and flat-term hypotheses are explicit and the edge cases `P^{a-1}=0`, `d^{a-1}=0`, the zero ring, and a field give the claimed zero or ordinary homology maps.
- Step 1: checked against `lem-weil-pbc-tor-long-exact-first-variable`, `def-weil-pbc-flat-ring-map`, and `def-weil-pbc-tor-modules`; those statements provide the exact Tor segment, flatness criterion, and resolution homology identification used.
- Step 2: checked against `lem-weil-pbc-tensor-right-exact`, `def-pc-acyclic-complex-modules`, and `def-pc-tensor-complex-sheaves`; right exactness gives the lift and the differential identities give well-definedness and containment in the kernel.
- Step 3: checked against the same tensor and complex definitions; the lift of a kernel element is a cycle because the inclusion of the image module is injective before tensoring, exactly as the step states.
- Step 4: checked against the Tor long-exact node and Tor functoriality; the composite is a surjection and its construction is natural in `N`.
- New nodes: none; B1--B7 and duplicate/Mathlib-node checks are vacuous. Existing dependency nodes were searched in `dag/nodes` and no replacement node was created.
- Mechanical check: `deliver.py ... --no-push` passed preflight (`aa71bf105`).

## Source error

The imported source label is not an exact statement match. More on Algebra Tag 0653 (`lemma-last-one-flat`) assumes a bounded-above flat complex with Tor-amplitude in `[a,b]` and concludes that `Coker(d^{a-1})` is flat; it does not state the general natural surjection in this item. The item’s surjection is the standard Tor exact-sequence consequence recorded in the existing generic Tor and tensor nodes. The target statement was not changed because it is fixed by the DAG item; this citation discrepancy must be recorded by the maintainer for source review.

Changes made in this second reading: added the explicit source-error record and the step-by-step audit; no node or proof text required correction after checking the cited statements.
