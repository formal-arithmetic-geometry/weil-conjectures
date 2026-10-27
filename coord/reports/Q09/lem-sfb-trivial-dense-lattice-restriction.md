## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trivial-dense-lattice-restriction.json`: statement, now split; unchanged statement and statement dependencies, four complete proof steps, existing-node citations only. The five executed Mathlib searches from this session are appended without deleting the imported searches. No Mathlib match for the item.
- `citations.json`: five step/node entries, with quotations checked verbatim against the current cited statements.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0. No unit file changed: this item is not its unit's key statement. No Lean source was written and no compiler, Lake, global build, or local preflight script was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, dense/trivial lattice language, and denseLattice/trivial exterior names. The hits were unrelated exterior powers and an affine-line middle-extension statement, not this theorem. Existing `lean/Sheaf/` implementations attached to prerequisite nodes are statement material, not evidence of a completed attachment for this item.

## WANTED

WANTED: a human-authored reference for the canonical dense integer lattice restriction theorem for ordinary internal modules over the all-continuous norm-topological algebraic closure coefficient ring, for lem-sfb-trivial-dense-lattice-restriction. The current blueprint paragraph (3) does not state this theorem. This delivery is explicitly an agent proof assembled from the existing DAG statements; it does not pretend that the blueprint or an SGA theorem supplies this analytic assertion. The analytic content remains in the already existing norm-topological exterior-model node.

## Findings and corrections

The imported item is an agent-created extraction from paragraph (3), not a theorem literally in that blueprint paragraph. Its statement was coherent and was retained exactly. Its proof was empty. I supplied the canonical-map proof rather than just an abstract isomorphism of cohomology groups. In particular, both exterior-model statements specify their actual derived maps and the same positive coordinate-class convention. This avoids treating an arbitrary exterior identification as restriction-compatible.

The current ancestor command prints `blueprint.from.node = None`; I retained the inherited null ancestor and via chain, and retained the precise non-unspecified paragraph reference. Whole-blueprint searches for `exterior` and `dense lattice` gave no same-statement blueprint node (the latter had zero hits; the former concerned exterior powers elsewhere). Whole-DAG search for coordinate cups, exterior cohomology and dense lattices found the exact existing prerequisites used here. No new node or duplicate was introduced. The unit record currently comes from the older six-functors location; the item's explicitly named main-20261015 source is the current direct-images proof, which I read and followed for the inherited paragraph-(3) expansion. No unit route or chapter-level statement changed.

The existing searches and citations were retained. New searches actually executed through msearch.py were two LeanFinder phrasings, Loogle `"Condensed", "invariants"`, a dense/PadicInt cohomology/invariants grep, and LeanSearch. All services returned successfully. I read the hits: the first semantic search returned condensed free/solid and discrete-module functors; the second returned ordinary Rep group-cohomology inflation/restriction and low-degree statements; LeanSearch returned p-adic integer identifications, solid/discrete condensed-module facts and a complex truncation restriction. These do not concern the specified internal coefficient ring and canonical derived restriction. Loogle and grep returned zero hits. The query text in the node agrees with searches.jsonl.

## Unfinished work

None for this one-level split. Existing prerequisite nodes may still require proofs; this delivery reuses their statements, as stage 1 requires. No new obligation has been disguised as a proof or as a Mathlib leaf.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs to distinguish. In particular I reused `lem-sfb-trivial-ladic-derived-exterior`, `lem-sfb-discrete-lattice-cup-exterior`, `lem-sfb-condensed-derived-restriction-calculus`, and the existing Mathlib leaf `lem-sfb-finite-dimensional-linear-map-continuous` rather than creating any coordinate-comparison or finite-sum lemma.

## Review by Q09

I read the current item, the chapter and unit records, the main-20261015 direct-images proof paragraph (3), and the complete statements and proofs of both exterior-model nodes and the restriction-calculus node. The blueprint's paragraph (3) discusses the open-immersion coefficient input; it does not give a canonical dense-lattice theorem. Accordingly the proof origin is agent. I read the finite-dimensional continuity node and its Mathlib declaration at `Mathlib/Topology/Algebra/Module/FiniteDimension.lean:283`; its complete, nontrivially valued base field hypothesis is satisfied by the finite extension E, not inferred for Omega. There are no new nodes whose source or standalone statement needs review.

Step 1 uses exactly the two exterior statements. The l-adic statement allows F=E and F=Omega with the extended norm topology, including noncomplete Omega, and uses the actual coordinate-cup map. The discrete-lattice statement allows any commutative condensed ring, so applies to C_F; it too specifies the derived map, the positive character normalization, and the empty unit. Both sources of these maps are the identical finite zero-differential sum indexed by subsets. These statements therefore say everything taken from them; no bar-resolution or continuous-cochain acyclicity is borrowed from their proofs.

Step 2 uses the restriction calculus's statement that the invariant-inclusion-normalized derived transformation sends [a] to [a composed with iota], preserves its unit and ordered products. On every integer tuple a_i composed with iota equals n_i times 1_F, and pointwise the same identity holds for all profinite parameters. Consequently the two maps out of each shifted-ring summand agree, including the empty summand. The finite biproduct universal property gives b chi_L = chi_D in the derived category itself. Inverting chi_L gives an explicit inverse factorization; there is no uncited comparison theorem in this step.

Step 3 uses the finite-dimensional continuity statement on the two E-linear basis maps. I checked finite dimension, Hausdorffness and completeness of E on both source spaces. For Omega I do not apply that theorem over a noncomplete base field: scalar-extended coordinates have the stipulated finite product topology; a change of coordinates and its inverse are finite matrices of elements of F, hence continuous by the topological field operations. The finite sum formula and the coordinate functions give mutually inverse continuous maps. Applying them to continuous S-valued sections is natural by precomposition, is C_F(S)-linear by evaluation, and is equivariant because every action is trivial. Thus this is an actual isomorphism in each action category. No projection formula, arbitrary direct-sum preservation, or assertion that continuous sections preserve a nonsplit quotient is being used.

Step 4 uses additivity and naturality exactly as stated in the calculus. Naturality with the chosen finite inclusions/projections forces each matrix entry of restriction: scalar b on the diagonal and zero elsewhere. The corresponding matrix of b inverses is a two-sided inverse. Naturality with the basis isomorphism conjugates it to the requested canonical map. Only finite biproducts are used, so no filtered-colimit or infinite-product claim is hidden. The statement's r=0 case follows from the calculus's identity normalization for trivial groups, and W=0 follows because additive functors preserve the zero object.

I checked B--E against the actual files. There are no new statement-only nodes, no new terminology or sources requiring definition nodes, no Mathlib-leaf claims added, no unit-route tool use, and no circular reference to the parent comparison theorem. Each proof dependency is exactly a node used by one of the four steps. Each step is shorter than 2000 characters. The elementary coordinate and finite-matrix arguments are written out; the steps are conservatively marked non-elementary because they use the named input theorems. No source is cited in place of a required node. Every citations.json quotation is a verbatim substring of the corresponding current node statement.

Small cases: r=0 yields the identity and the exterior source has just its empty summand; r=1 sends the degree-one coordinate x to the integer coordinate n with positive sign; r=2 sends alpha_1 cup alpha_2 to delta_1 cup delta_2 in the same order, with no permutation sign. W=0 gives the unique map of zero objects; dim W=1 recovers the scalar calculation. Both choices F=E and F=Omega retain the norm topology throughout. None of the arguments completes Omega, replaces it by a filtered-union topology, or assumes a single finite extension contains the images of all continuous functions. I found no statement dispute and made no change to the item statement.

## Delivery check repairs

The first dry run rejected only the short quotation for step 4 (it required at least 40 characters). I expanded it verbatim to include the additive derived-functor sentence and the full restriction paragraph, so it explicitly supports additivity, naturality and the trivial-group identity. The mathematical proof did not change.
