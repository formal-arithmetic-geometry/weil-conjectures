## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-colimit-matrix-cokernels.json`: statement, split; no exact Mathlib match. The statement and inherited metadata/searches are retained. Eight proof steps now give every conclusion.
- `citations.json`: one verbatim statement quotation for every use in every step.
- This report. No new nodes, no new Mathlib leaves, no unit edits, no Lean edits or compilation.

Attachments: none. Searching the supplied `lean/WeilConjectures/` for the blueprint tag, entrywise conjugacy, mapBiproduct, PreservesCokernel, and matrix/cokernel combinations found component constructions and specialized uses, but no project declaration with all the item's hypotheses and conclusions. Upstream sorried declarations were not treated as proofs.

WANTED: none.

The item was unsplit and its sandbox contained no node, report, or previous search record before this attempt. I copied the live node. The imported statement is true as written, including both zero ranks; there is no statement dispute or correction. The blueprint only says that pullback preserves the local coefficient models on strata, not this categorical calculation, so `proof_origin.by` is `agent`. I expanded that calculation without changing the chapter or unit route. The existing `lem-sfb-preserving-colimits-additive` is a Mathlib leaf and supplies the only non-elementary ingredient. I did not create nodes for elementary consequences of the coproduct/cokernel universal properties.

Nothing remains unfinished in this one-level split.

## Sources and searches

I read the chapter and unit records for `sec-six-functors-basics` and `sk-prop-proper-base-change-unbounded`, the current main-20261015 proof of `det-proper-base-change-unbounded-pullback`, and the parent `lem-sfb-scalar-matrix-inverse-image`. The exact blueprint place is the paragraph “Constructible complexes”, “via the local coefficient models on strata”. The parent requires precisely this finite-coproduct comparison, the scalar entry test, and the projection-compatible cokernel isomorphism. Its finite-presentation route is preserved.

For additivity I read Stacks `homology.tex`, Tag 010N, `lemma-exact-functor` (1), with its hypotheses and proof, and Mathlib `CategoryTheory/Preadditive/AdditiveFunctor.lean:316–334`, especially `CategoryTheory.rightExactFunctor_le_additiveFunctor` at 330. For the elementary universal-property calculations I read Stacks `categories.tex`, Tag 002F, `definition-colimit`, and its following uniqueness observation. The source explicitly includes coproducts, coequalizers, and the empty colimit as special cases. I opened and read the statements of all three cited DAG nodes: `lem-sfb-preserving-colimits-additive`, `def-sp-abelian`, and `def-weil-pbc-category-colimit`.

The whole-DAG title/statement search found the existing additivity leaf. Blueprint searches for “biproduct”, “cokernel”, “finite colimit”, “entrywise conjugate”, and “matrix” found no blueprint node stating this complete comparison; `same_as` remains empty. The ancestor command returns `det-proper-base-change-unbounded-pullback`, as already recorded. No new node was created, so there is no new-node duplicate or Stacks-tag collision to justify.

All five Q57 Mathlib searches were run through the required `msearch.py` and are retained in `searches.jsonl` and appended to the item's searches without modifying the inherited queries. LeanFinder was tried with two different formulations. Loogle found `Functor.mapBiproduct`; grep found its definition and `PreservesCokernel.iso` with its projection equation. LeanSearch found those cokernel comparisons and finite-colimit preservation results. I read `Limits/Preserves/Shapes/Biproducts.lean:265–286`, `Limits/Preserves/Shapes/Kernels.lean:230–282`, and `Preadditive/Mat.lean:348–412`. The first gives the object comparison; the second gives only the image cokernel comparison; `Mat_.additiveObjIsoBiproduct_naturality` has domain `Mat_ C`. None is an exact statement or a one-line specialization yielding this whole item and its specified object-isomorphism conjugacy. The proof below combines their mathematical ingredients explicitly instead of treating the item as a leaf. The second phrasing returned Gaussian elimination and cokernels of biproduct injections/subtype inclusions, which concern particular maps, not arbitrary entrywise-intertwining matrices.

## Not duplicates

No new nodes. The existing additivity Mathlib leaf is cited, not duplicated. The existing scalar-matrix inverse-image lemma is the parent application and is not cited backwards.

## Review by Q57

I checked delivery-errors B–E with the actual source statements open. The statement is self-contained: its biproduct relations, zero-rank convention, and cokernel universal property are written explicitly. Its two statement dependencies supply abelian categories and colimits; there is no extra coefficient category, size assumption, additive-functor assumption, or exactness assumption smuggled into it. No new statement-only nodes or hollow definitions are introduced. The TeX is escaped once in JSON. Inherited fields and the statement are unchanged.

Step 1 uses `lem-sfb-preserving-colimits-additive`, whose statement says exactly that finite-colimit-preserving functors between abelian categories preserve sums of parallel morphisms. Its hypotheses agree with the item's. `def-sp-abelian` supplies the additive abelian groups in which cancellation turns H(0)=H(0)+H(0) into H(0)=0. I checked the source Tag 010N and its right-exact interpretation; this step does not assume that H is exact.

Step 2 uses the universal cocone and uniqueness statement of `def-weil-pbc-category-colimit` and the finite biproducts in `def-sp-abelian`. The indexing category is explicitly the finite discrete category Fin(r). The coproduct structure with legs iota_j composed with e is justified by precomposition with e inverse. Thus the comparison is the one required by the item, including the initial-object comparison at r=0.

Step 3 uses the same two definitions. It verifies the projection equation on each mapped injection, where the two values are e or zero. This proves the compatibility rather than assuming that H preserves the product structure. Coproduct uniqueness is exactly the cited colimit statement. No faithfulness of H is used.

Step 4 uses `def-sp-abelian` only for its preadditive structure and the finite biproducts already specified in the item. It writes the finite sum defining a matrix morphism and inserts both biproduct identities to prove uniqueness. This is a finite distributive calculation, not a missing lemma about matrices. Empty sums and the zero-object identity are explicitly included.

Step 5 again uses the two definitions. Its displayed equation checks both sides against each pair of source injection and target projection using the entrywise hypothesis. It then writes out why the projections detect equality and invokes source coproduct uniqueness. I checked every domain and codomain: both compared maps have source H(X^m) and target Y^n. There is no implicit assertion that H preserves entries or sums beyond what has already been proved.

Step 6 uses the colimit definition and the cokernels in `def-sp-abelian`, with the cokernel universal property as explicitly stated in the item. I wrote the cocone leg at the source of the parallel pair, which is forced to zero, so the identification of a cokernel with the coequalizer of p and 0 is actually proved. The indexing category has two objects and two nonidentity arrows, hence is finite and small. It follows directly from the preservation hypothesis that H(kappa_p) has the required unique factorization property. No general preservation-of-cokernels theorem is used without a node.

Step 7 uses the cokernel structure of `def-sp-abelian` and the universal properties already proved in step 6 or given in the statement. Both annihilation equations are written. I checked the orientation of the inverse square: E_n inverse composed with q equals H(p) composed with E_m inverse. The maps u and v are therefore well typed with the promised projection equations.

Step 8 uses the same cokernel structure. It computes vu and uv after their respective projections and uses uniqueness, so it neither assumes preservation of epimorphisms nor cites a uniqueness theorem absent from a node. It also establishes uniqueness of u with its stipulated equation.

For each step, `citations.json` quotes the actual part of the cited statement used, not its proof or a reference tag. The only non-elementary step is step 1, which cites the existing additivity leaf. The other steps are explicit applications of the definitions and displayed identities. Every step is shorter than 2000 characters; none hides an independent lemma or a “standard” comparison. I checked that proof_deps is precisely the union of step uses and that no dependency runs through the scalar-matrix parent, so the split adds no cycle or route departure.

I tested m=n=0 (all objects and maps are zero and the unique comparison is an isomorphism), m=0 (the cokernel is the target with its identity projection up to unique isomorphism), n=0 (the cokernel is zero), the zero functor (e then forces Y to be a zero object), rank one with e arbitrary, and a nonfaithful right-exact functor such as tensoring abelian groups with Z/2. The calculations need neither positive ranks nor left exactness. No statement correction was needed.

The required server dry run is the final mechanical check; delivery is performed only after it exits OK.
