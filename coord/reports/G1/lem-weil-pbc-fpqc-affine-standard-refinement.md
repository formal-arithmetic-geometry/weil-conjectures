# Stage-1 split: lem-weil-pbc-fpqc-affine-standard-refinement

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-fpqc-affine-standard-refinement.json: split, 3 steps, 0 new nodes.
- citations.json: six verbatim citations for the four distinct dependencies.
- report.md: this report.

## Attachments

None. AlgebraicGeometry.Scheme.exists_finite_affine_flat_of_mem_fpqcTopology in WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:143 is sorry-free and closely related, but its conclusion is a finite affine family in a covering sieve. It does not assert the required faithful flatness of the product of the selected coordinate rings for the given covering family, so it is not an exact attachment.

## WANTED

The repository copy lacks literature/stacks-project/; I read the primary Stacks Project pages online for Tags 022B, 03N0, 01U5 and 00HQ. Their local .tex files are wanted to reproduce that source check offline. The proof is the direct argument from those cited statements, not an unsupported replacement route.

## Changes and limitations

The item was unsplit. Its statement is correct against 022B and the reduction in 03N0, so I kept it. I supplied the finite-cover choice, affine flatness and finite-product flatness, then the prime-contraction argument and the faithful-flatness criterion. No new node was needed. The blueprint.from.place already names the exact 03N0 sentence; a whole-blueprint search for "finite affine flat" and "fpqc covering" found no equivalent blueprint node, so same_as stays empty. Searches made with msearch.py were recorded with their actual queries; LeanSearch returned HTTP 500 and is marked unavailable. The closest Lean source theorem is the sieve refinement above, not an attachment.

## Review by G1

I read Stacks 022B, which gives both flatness of each covering arrow and, on the affine open $T$ itself, finitely many affine opens whose images cover $T$. Step 1 cites precisely that defining sentence in def-weil-pbc-fpqc-covering; its index map need not be injective, which permits repeated covering members. For $T=\varnothing$, the definition allows an empty finite family and the product is the one-element ring, whose spectrum is empty.

I read Stacks 01U5 and the statements of lem-weil-pbc-flat-morphism-affine-criterion and lem-weil-pbc-finite-product-flat-modules. Step 2 uses the criterion with target affine open $T$ and source affine open $V_j\subset T_{a(j)}$; these are exactly its affine-chart hypotheses. The fpqc-cover definition supplies flatness of $f_{a(j)}$. The finite-product node explicitly states flatness of the product of flat modules, including the empty product. These statements give flatness of the ring map in the sense of def-weil-pbc-flat-ring-map.

I read Stacks 00HQ and lem-weil-pbc-flat-surjective-spectrum-faithfully-flat. Step 3 uses the cover's image equality from def-weil-pbc-fpqc-covering. Given a point of $\operatorname{Spec}R$, a chosen $V_j$ supplies a prime of $A_j$ above it; inverse image along the coordinate projection from $\prod A_k$ is prime and contracts to the original prime. Thus the spectrum map is surjective, which is the hypothesis stated by the 00HQ node; step 2 supplies its flatness hypothesis. This checks the empty-base case as well. I corrected citation JSON escaping after verifying each quote as a literal substring of its cited node's statement. No statement was weakened, no clause was moved into a new node, and the proof does not cite a node merely for facts in its proof.

## Not duplicates

No new nodes were created.

## Second reading by G1

- Item statement: checked against the affine fpqc refinement in Stacks Tags 022B and 03N0; the finite affine selection and faithfully-flat product conclusion match, including the empty affine case.
- Step 1: checked against `def-weil-pbc-fpqc-covering`; its finite affine-open image-cover and flatness clauses supply exactly the choices used, and the empty family is valid for the empty scheme.
- Step 2: checked against `lem-weil-pbc-flat-morphism-affine-criterion` and `lem-weil-pbc-finite-product-flat-modules`; the affine-chart hypotheses apply to each selected open and the finite, including empty, product is flat.
- Step 3: checked against `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat` and the covering clause; a prime over each point pulls back through a coordinate projection to a prime of the product, proving spectral surjectivity.
- New nodes: none; all dependencies are existing definitions, Mathlib leaves, or existing statement nodes, so no B1-B7 or duplicate issue applies.
- Edge cases checked: empty scheme and empty index set, a field base, and singleton finite selections; the conclusion behaves correctly in each case.
- Changes: none to the item, proof, or citations; this section records the independent second reading.
