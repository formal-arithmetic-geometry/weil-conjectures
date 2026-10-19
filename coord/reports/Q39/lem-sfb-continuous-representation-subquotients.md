# Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-representation-subquotients.json`: item split into five proof steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dimensional-subspace-closed.json`: Mathlib leaf, `Submodule.closed_of_finiteDimensional` and `LinearMap.isClosedEmbedding_of_injective`.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dimensional-quotient-open.json`: Mathlib leaf, `Submodule.isOpenQuotientMap_mkQ` and `Submodule.isOpenMap_mkQ`.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dimensional-linear-map-continuous.json`: Mathlib leaf, `LinearMap.continuous_of_finiteDimensional`.
- `citations.json`: verbatim quotes for every cited node in every item step.

Attachments: none. No sorry-free project declaration states the item exactly; the source search found only related lisse-representation declarations and no declaration tagged with this item.

WANTED: none.

The imported statement agrees with Bhatt–Scholze, *The pro-étale topology for schemes*, Corollary 6.8.5, proof, p. 60. I kept its finite extension $E$, profinite group $\Pi$, continuity, topology, exact sequences, and universal-property clauses unchanged. The proof makes explicit the finite-dimensional topological linear algebra implicit in the source sentence that the representation category admits kernels and cokernels.

## Not duplicates

- `lem-sfb-finite-dimensional-subspace-closed` vs `cor-galois-lisse-representations`: the existing node concerns an exact equivalence for finite locally constant sheaves and finite discrete representations; it does not state closed finite-dimensional subspaces or topology.
- `lem-sfb-finite-dimensional-quotient-open` vs `lem-sfb-compact-hausdorff-surjection-quotient`: the existing node treats compact-to-Hausdorff continuous surjections, while this node states the open quotient map for module quotients.
- `lem-sfb-finite-dimensional-linear-map-continuous` vs `cor-galois-lisse-representations`: the existing node has exactness of a fibre equivalence, while this node gives continuity of arbitrary finite-dimensional linear maps.

## Review by Q39

I read the item node, the unit `sk-lem-coefficient-heart`, the chapter `sec-six-functors-basics`, the parent closure proof in `det-lem-coefficient-heart-closure`, and the cited Bhatt–Scholze passage. I also read the Mathlib source at `Topology/Algebra/Module/FiniteDimension.lean` lines 283, 530, and 565 and `Topology/Algebra/Module/Basic.lean` lines 319–322. Step 1 uses the coefficient-extension statement for completeness and the closed-subspace leaf for the topology on $U$; the restricted action is the ambient action followed by the closed embedding. Step 2 uses the open quotient leaf and explicitly descends the action along $\Pi\times V\to\Pi\times(V/U)$, using $\Pi$-stability of $U$. Step 3 checks that kernels, images, and quotients are stable finite-dimensional subspaces and that all linear maps are continuous using the finite-dimensional continuity leaf. Step 4 checks underlying vector-space exactness and equivariance. Step 5 checks the kernel and cokernel universal properties, including continuity of the unique factor maps. I tested $U=0$, $U=V$, $V=0$, trivial $\Pi$, $h=0$, an isomorphism, injective and surjective maps, and split maps; all clauses reduce correctly. The three Mathlib searches for each new leaf were run with `msearch.py` and recorded verbatim in the node files.

What was corrected: the original node had no proof split. I added only the three genuine Mathlib topological prerequisites and kept the imported statement, dependencies, source, and blueprint ancestry aligned with the parent route. No SGA source is used and no off-unit tool use is needed.

What remains unfinished: nothing within this stage-1 item.
