# Stage-1 report: lem-sfb-space-inverse-modules-near-special-fibre

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-modules-near-special-fibre.json`: statement, split into five proof steps; original statement and statement dependencies retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-derived-limit.json`: statement-only, unsplit; no Mathlib match. Bounded nonnegative derived quasi-coherent inverse limit with its projections.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-polynomial-model.json`: statement-only, unsplit; no Mathlib match. Finite-free polynomial-chart models and their localized K-flat computation.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-affine-base-change.json`: statement-only, unsplit; no Mathlib match. Canonical derived reduction on qcqs etale charts.
- `citations.json`: one verbatim statement quote for every cited node in every item proof step.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag and the notions inverse coherent modules, nilpotent inverse limits and algebraization. The algebraization hits concern formal ring glueing, not the assertion about arbitrary algebraic spaces and proper-support infinitesimal sheaves. There is no exact project declaration to attach. No Lean was written or compiled.

## WANTED

None. All needed sources are in the read-only literature tree.

## What needed correction

The item had no proof or proof dependencies. Its statement agrees with spaces-flat.tex Situation 0CX4 and the existence conclusion of Lemma 0CX9. No statement dispute or changed hypothesis was necessary. I supplied the three derived inputs, expanded the source's maximal-rank cancellation, and used the single global module H^0(K) so that gluing and transition compatibility do not depend on unrelated choices of local realizations.

The inherited blueprint ancestor command returns None, as it does for the parent's accepted split: the created.item chain ends at a Lean-module item. I preserved the inherited null ancestor and via list, named the supporting part of proof (3) of the current `det-thm-sf-ctf-stability-direct-images`, and filled each new node's exact source place. The current blueprint was read in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including the direct-images proof. This work stays in the existing coherent-family/Quot effectivity prerequisite chain; it does not change the six-functor route.

## Searches and existing material

Before creating the nodes I searched the whole DAG for Tags 0CX4--0CX9, 0CST, relative pseudo-coherence, derived inverse limits, and polynomial finite-free models. I used `tools/blueprint_refs.py ancestor` on the item and `search` for inverse limit, pseudo-coherent/pseudo-coher, 0CX, proper support, polynomial, and base change. None of the imported blueprint statements gives these infinitesimal derived-limit assertions. Existing nodes for relative pseudo-coherence on charts, flat ambient embeddings, and affine derived equivalences were opened. Their statements take an already relatively pseudo-coherent object or assert a general equivalence; they do not establish the essential pseudo-coherence of this inverse system. I reused the existing affine etale realization and open-image theorem in the proof.

For each new node, the required msearch command ran two LeanFinder phrasings, LeanSearch, Loogle, and Mathlib grep. Exact queries and outputs are recorded in the node and `searches.jsonl`; full returned hits are also retained in the sandbox's search result files. All these services answered. The hits include ordinary sheaf limits, t-structure vanishing definitions, scheme inverse-limit section lemmas, Noetherian adic-completion flatness, local cohomology, ordinary tensor/direct-limit comparisons, and stability of etale maps under base change. None states one of the new nodes or specializes to it in one line. The item's inherited Mathlib searches were retained and their hits read; finite-presentation predicates on sheaf modules do not prove realization of an infinitesimal tower.

## Not duplicates

lem-sfb-space-inverse-module-derived-limit vs lem-sfb-space-inverse-modules-near-special-fibre: 0CX5 supplies a bounded derived object with projections; the item asserts existence of an ordinary finitely presented module on a neighborhood, which needs the later polynomial cancellation argument.

lem-sfb-space-inverse-module-polynomial-model vs lem-sfb-space-inverse-modules-near-special-fibre: the shared reference to 0CX9 concerns its intermediate polynomial complex, possibly with positive cohomology away from the infinitesimal locus; it gives neither a neighborhood nor an ordinary realizing module. The item proves those by cancellation and passage to H^0.

lem-sfb-space-inverse-module-polynomial-model vs lem-sfb-space-relative-pseudocoherence-etale-locality: the latter (0CSX) transfers a relative pseudo-coherence hypothesis between charts; it does not prove that the inverse limit of a compatible flat proper-support tower has that property or supply its finite-free model.

lem-sfb-space-inverse-module-polynomial-model vs lem-sfb-flat-ambient-relative-pseudocoherence: the latter (09UU) compares relative pseudo-coherence with absolute pseudo-coherence under an embedding; our input establishes it for the derived limit of the specified tower and records the polynomial model used for reductions.

lem-sfb-space-inverse-module-polynomial-model vs lem-sfb-perfect-tests-detect-pseudocoherence: the latter uses perfect tensor tests for a separated flat finitely presented scheme; our ambient algebraic space need not be flat, and the tower-derived pseudo-coherence assertion is absent from it.

No existing node shares the affine-base-change node's source Tag 0CX8 or states its comparison. The item itself mentions the range 0CX5 through 0CX9; its ordinary existence assertion differs from this canonical derived comparison.

## Review by Q47

I read spaces-flat.tex Situation 0CX4 and Lemmas 0CX5--0CX9 with their proofs. For the derived-limit node I also read spaces-perfect.tex Example 0CST: the quasi-coherator right adjoint constructs products/derived limits in D_QCoh, and its boundedness argument supplies precisely boundedness and vanishing in negative degrees. I did not identify this product with the underived product of quasi-coherent modules.

For the polynomial-model node I checked 0CX7 and the actual model used in the proof of 0CX9, and read 0CSX in spaces-more-morphisms.tex and 09UU in more-morphisms.tex. The polynomial ambient ring is smooth and flat over A, even when X itself is not flat. A finite-free complex bounded above over that ring, or a principal localization of it, is K-flat over A; the statement includes this computational property because it is necessary for the later raw tensor calculation. It states the model as an isomorphism in the derived category, not merely an agreement of cohomology groups. The principal-localization assertion is localization of that same affine model. This is an input about the actual inverse limit, substantially weaker than the item's ordinary finite-presentation realization. It is left unsplit, with no proof sketch inserted into its statement.

For the affine-base-change node I read 0CX8 and its proof through the canonical perfect-test comparisons of 0CX6. The source uses the derived category D(A_n), and I kept that category rather than inventing a stronger change of coefficient category. The isomorphisms are the maps induced by the limit projections. Their naturality and transition compatibility are those of these same maps. Quasi-compactness and quasi-separatedness are hypotheses on the etale chart; the affine charts used in the item satisfy both, and their base changes remain affine.

Step 1 uses exactly the derived-limit node's existence, bounds and projection relation. It does not assume its H^0 is already finitely presented or already recovers the tower. Step 2 uses the polynomial-model node for the finite-free representative and raw tensor computation, the affine-base-change node for the reduction isomorphism, and `lem-sfb-affine-etale-derived-module-realization` for exact faithful realization and its derived quasi-inverse. I opened that existing statement: it explicitly identifies the module derived category with etale D_QCoh, identifies cohomology sheaves, and gives Gamma of an associated module. The chart B is chosen finitely presented over A using X's chartwise finite-presentation hypothesis, so a finite polynomial presentation is available. No smoothness of X is assumed.

Step 3 is the explicit finite matrix argument, rather than a hidden invocation of generic freeness or Nakayama on an unknown finite module. At a prime of the closed fibre the highest reduced cokernel vanishes, so a maximal minor is invertible on a neighborhood containing the chosen point. Writing the matrix as [I D] gives the free kernel and a contractible identity summand. This also explains why the cancellation survives every reduction. Repeating reduces the finite positive upper bound to zero. A split kernel was not silently assumed free; the invertible-minor coordinates prove freeness. No new lemma node is needed for this routine written-out matrix argument.

Step 4 uses the same existing affine equivalence and the base-change node. Its finite presentation is the explicit cokernel of the last two finite-free terms. Tensoring that presentation with the quotient B' is right exact and yields a presentation over B', since the quotient ideal acts by zero on C. H^0 of a complex concentrated in nonpositive degrees commutes with this scalar extension by that same cokernel calculation; no unjustified flatness of H^0(K) is used.

Step 5 uses `lem-a1-space-etale-open-image`, whose statement I read in full: representable etale image is an open subspace and the chart surjects etale onto it. Finite presentation in the item is defined etale locally, so the resulting covering family proves it directly. All local modules are restrictions of one F_*, and all comparisons are induced by its fixed a_n; there is no uncited effectiveness-of-descent claim. Local inverse maps glue by uniqueness. On a pure tensor the two transition composites both send m tensor b to b a_(n-1)(m), proving the specified compatibility. The two existing cross-unit statements are declared generic tool uses in split_report; neither replaces a six-functor step.

I checked B--E of delivery-errors.md against the files and sources: all new nodes introduce their own base, schemes/spaces, inverse system, modules and derived notation; every non-elementary cited fact has a node whose statement gives it; definitions are not cited for unrelated preservation theorems; there are no proofs in unsplit nodes, invented searches, SGA references, or altered statements. `citations.json` was constructed only after testing each quote as a literal substring of the opened statement. All proof steps are under 2000 characters.

Small cases checked: zero modules, zero polynomial variables, zero free ranks, a complex with upper bound already nonpositive, and X_0 empty. The empty case is explicit in the proof. A constant system yields an ordinary sheaf, consistent with the construction. For a nonconstant locally nilpotent tower, the only prime argument is at a point containing ker(A -> A_1); no uniform nilpotence exponent or adic/Noetherian hypothesis is used. Neither properness nor flatness of the eventual F is claimed here; those are later inputs of the parent's effectivity theorem.

## Unfinished work

None within the one-level stage-1 assignment. The three new statement-only nodes are deliberately unsplit and ready for their own stage-1 workers. The unit realization record was not changed because this item is not the unit's key statement.

## Validation

Initial server review_split passed. The required full delivery dry run and final push are run after this report; their final outcomes are recorded below.
