## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-lattice-injective-koszul-acyclicity.json`: split in six steps; statement unchanged; no Mathlib match.
- `citations.json`: ten step/node entries, each checked against the literal current statement.
- `report.md`: this report. No new nodes or Mathlib leaves.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id, lattice Koszul terminology and cubical constructions found no matching declaration. The many unrelated geometric Koszul constructions do not state this internal-equivariant assertion.

## WANTED

WANTED: a published treatment of the sectionwise injective lattice Koszul argument for condensed module sheaves, for lem-sfb-lattice-injective-koszul-acyclicity. The blueprint only supplies the surrounding tame-boundary route. The proof is explicitly marked agent-written; its categorical inputs already have DAG nodes, and the free section test is supported by Stacks below.

## Findings and changes

The item's statement is sound. Its source place mentions flatness of the free test module (Stacks 03EV); flatness is true but unnecessary here. The existing cubical node states split exactness for **every** internal module Q, not just R. Substituting the free test module Q_U gives an exact equivariant complex without a tensor-flatness argument. Injectivity extends maps from its boundary image, and internal tensor-Hom identifies its ordinary equivariant Hom with the requested section complex. Neither projectivity of a free sheaf nor exactness of section evaluation is assumed. No clause of the item was moved into a new node.

The inherited blueprint ancestry is broken above the created lattice chain: `tools/blueprint_refs.py ancestor lem-sfb-lattice-injective-koszul-acyclicity` reports `None`. I retain the existing null ancestor, via chain and precise paragraph place, and document the result in split_report. The item is not the unit's key node; the unit realization fields are untouched. The unit route stays the algebraic lattice input below direct-image paragraph (3).

## Search record

I read the inherited searches and reran the item with logged msearch commands: two semantic phrasings, a Loogle injective/exact query, the Koszul/injective/invariant regex, and LeanSearch. The services were available for the new queries. The semantic hits were ordinary Rep bar and finite-cyclic resolutions, module regularity and unrelated cotangent sequences. Loogle/LeanSearch found `CategoryTheory.ShortComplex.Exact.descToInjective`, a generic extension theorem: the corresponding argument here is written explicitly from the already cited definition of injective, so no new node is needed. None gives the internal complex and its sectionwise acyclicity in one specialization. The inherited unavailable LeanSearch result is retained as unavailable. Query texts and actual logged summaries are preserved in mathlib_searches.

I searched the entire DAG and blueprint for Koszul, lattice, free representable evaluation, and injective exactness. Existing nodes supply all ingredients. The blueprint Koszul hits concern other constructions, especially adic completion, and do not duplicate this item. The relevant free representable presheaf evaluation node and module sheafification node were read in full rather than using a bare fully faithful Yoneda claim.

## Not duplicates

No new nodes. Reused the cubical resolution, closed internal-module Hom, internal/section-ring equivalence, module sheafification universal property, free representable presheaf evaluation, injective definition, and derived-category definition.

## Review by Q07

I read the main-20261015 `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3), the chapter record, the unit record, and the existing cubical node's full statement. The blueprint gives the direct-image route, not this algebraic proof. I read Stacks `sites-modules.tex` Tag 03DI (`lemma-extension-by-zero` and `equation-map-lower-shriek-OU-into-module`), its explicit sum over arrows and generator map, and Tag 03EV (`lemma-j-shriek-flat`), distinguishing flatness from projectivity. Tag 03CY (`lemma-sheafification-presheaf-modules`) supplies exactly the universal property recorded by the cited module-sheafification node. No SGA source is used.

Step 1 uses the cubical node's assertion that forgetting the D-action creates kernels and cokernels. Finite biproducts act componentwise, so exactness is a short calculation. I checked opposite signs for deleting i then j, including the rank-two sign `(T_1-1)x_{2}-(T_2-1)x_{1}`. Equivariant maps commute with all the operators; invariants are killed by every generator difference.

Step 2 uses the actual adjunction in `def-sfb-modobj-internal-hom`, not merely a name for internal Hom. The cubical node explicitly identifies Q tensor L(R) with L(Q), with translation. Conjugation invariance of the transpose is precisely equivariance of the bilinear map when Q has trivial action. Evaluating each free orbit at zero and extending by T^v are inverse constructions. Naturality in every test module proves an internal-module isomorphism, not just a bijection on global points. This identifies complexes, not only their cohomology groups.

Step 3 uses the actual signed boundary displayed in the cubical node. Precomposing on [0,J] gives exactly the differential in the item; I checked that this convention adds no extra Hom-complex sign. Augmentation precomposition evaluates to f(1), the invariant inclusion. This also verifies naturality and the required inverse formula on generalized elements.

Step 4 uses three statements actually opened: the equivalence leaves all sections and restrictions unchanged; sheafification factors maps uniquely into module sheaves; and free representable presheaf evaluation has inverse s sent to restrictions s|phi. These give Hom(Q_U,M)=M(U), for variable ring-sheaf coefficients rather than constant coefficients. The two formulas commute with module maps, so step 2 applies to Q_U and identifies the whole augmented section complex. This does not require that evaluation be exact. These are generic tools; the declaration in split_report documents their use outside the unit.

Step 5 uses the cubical node for arbitrary Q_U, including the crucial underlying split exactness and creation of kernels and cokernels. For a positive-degree cocycle the boundary kernel equals the preceding image, so it factors through the image of the next map. The injective node says exactly that a map from a subobject into J extends along a monomorphism. Applying it to that equivariant image inclusion gives g with g partial = f. This is the explicit two-line proof of exactness of contravariant Hom into an injective, not an uncited theorem. At the top the next boundary is zero; at degree zero epsilon is a cokernel, giving unique factorization and injectivity of its Hom map. All these maps live in the equivariant abelian category: I never use the nonequivariant contracting homotopy as though equivariant.

Step 6 uses the cited definition of cohomology and quasi-isomorphism. Sectionwise lifting implies sheaf surjectivity onto the kernel; degree zero is exactly the fixed submodule. The argument handles r=0 (all relevant maps identities), r=1 (T_1-1), rank two (opposite deletion signs), zero coefficients/module, and the empty profinite object. There is no division by a coefficient and no assumption of a field, discrete coefficients or characteristic zero. Since there are no new statements, no additional edge-case hypotheses were introduced. Every step is under 1000 characters, so no long-step hidden lemma remains.

## Unfinished work

None for this one-level split. Existing dependencies remain independently queued as their own states require. No Lean was written and no compiler or build was run.
