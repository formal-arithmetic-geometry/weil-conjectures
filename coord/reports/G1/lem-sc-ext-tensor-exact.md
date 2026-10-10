# lem-sc-ext-tensor-exact

Files written: `dag/nodes/sec-picard-framework/lem-sc-ext-tensor-exact.json` (item, split); `citations.json` and this report. New nodes: none. Mathlib leaves: none.

Attachments: none. The source checkout has no declaration tagged `lem-sc-ext-tensor-exact` or asserting exactness of tensoring scheme modules by a finite locally free module. `IsFiniteLocallyFree.dual` and `tensorObj` in `WeilConjectures/AlgebraicGeometry/Modules/Dual.lean:180,186` state closure properties, not this exactness claim.

WANTED: `literature/stacks-project/modules.tex`, Tags 01AG, 01CB, 05NE, for `lem-sc-ext-tensor-exact`. The literature checkout is not present on this machine; I read the official Stacks online text of Modules Section 17.17, especially 05NE, and the complete statements and proofs of the already split DAG nodes for 01AG and 01CB. The proof follows those tagged results, specialized to finite free stalks.

The imported item had no proof. Its statement already allows the rank to vary between opens, which is necessary on disconnected schemes. The parent blueprint's exactness sentence is the place realized. Searches of the whole DAG and `blueprint_refs.py` found the two ringed-space tools already stated and no duplicate blueprint node for the item. There was no mathematical error in the parent proof and no unfinished part of this split.

## Review by G1

I compared the item with the parent's exactness sentence and with Stacks Modules 05NE: the hypotheses are a scheme and a locally free module on an open cover; 05NE needs only flat stalks, and a finite free stalk supplies them. The item's claim is slightly more concrete than the Stacks flatness criterion, but it has exactly the required hypotheses. No new node was needed, so B1-B10 were checked against the existing cited nodes rather than new statements.

Step 1 uses `def-weil-pbc-module-stalk`, whose statement makes the germ an $\mathcal O_{X,x}$-module and gives germ maps. The local trivialization is in the item's own hypothesis; taking germs of its basis and inverse is elementary. I checked that $x$ lies in the selected open and did not assume one global rank.

Step 2 uses `lem-weil-pbc-module-stalk-tensor`. Its statement gives the natural isomorphism $(\mathcal P\otimes\mathcal G)_x\cong\mathcal P_x\otimes\mathcal G_x$, including how germs of tensors map, so it applies to morphisms as written. The displayed basis map and inverse explicitly identify the latter with $\mathcal G_x^{\oplus d_a}$. The finite coordinate calculation is elementary; the tensor-stalk comparison is the cited non-elementary fact.

Step 3 uses `lem-weil-pbc-module-stalk-exact` clause (5) in both directions and the naturality clause of `lem-weil-pbc-module-stalk-tensor`. The former explicitly says a module-sheaf complex is exact exactly when all stalk complexes are exact; applied at each position, it covers both endpoints of a short exact sequence. Kernels and images of a finite direct sum are coordinatewise. No flatness theorem is invoked without a citation: exactness is proved directly for the finite free stalk. The two off-unit lemmas are recorded as generic tool uses in `split_report`.

I tested $d_a=0$ (the zero tensor functor), $d_a=1$ (identity functor), arbitrary finite $d_a$ (coordinatewise direct sum), and a disconnected $X$ with different ranks on components. Each gives an exact tensor sequence. I also checked the zero middle module and a nonsplit short exact sequence: the argument uses exactness of stalks and coordinates, not a splitting. The absent local literature was the only limitation; no statement or hypothesis was changed, and no repair was needed before preflight.
