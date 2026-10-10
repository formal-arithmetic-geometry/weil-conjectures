# Worker report: lemma-weil-pbc-etale-cohomology-continuity

## Change

- Marked `lemma-weil-pbc-etale-cohomology-continuity` split.
- Recorded the blueprint search as `same_as: []` and added the two blueprint proof places to `split_report.blueprint`.
- Kept the existing two proof paragraphs and their cited nodes. Removed `lemma-weil-pbc-fibre-product-limit` from `proof_deps`: neither paragraph uses a fibre-product limit, so it was not part of the union of step citations.
- No new DAG nodes and no Lean files were written.

## Source-first audit

I searched recursively under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the notion and for `(blueprint: `lemma-weil-pbc-etale-cohomology-continuity`)`. There is no declaration with that blueprint tag and no exact declaration of the inverse-limit comparison

`(colim j >= i) H^q(X_j,F_j) ≅ H^q(X,F)`.

The nearest related declaration is `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered` in `AlgebraicGeometry/Curve/Reductions.lean:68-84`. It has the different statement that cohomology on one qcqs scheme commutes with a filtered colimit of sheaves, and its proof is `sorry`; it is therefore not an attachment. The source also contains the section-continuity declarations in `AlgebraicGeometry/Sites/SectionContinuity.lean:74-123`, but those are the lower-level section result, not this cohomology theorem, and the main declaration there is `sorry`.

## Proof review notes

1. For surjectivity, `thm-weil-pbc-hypercover-cohomology` represents a class by a cocycle on a hypercover finite in each degree. Only the finite truncation through degrees `q+1` is needed. `lemma-weil-pbc-finite-hypercover-descent` descends that truncation to a stage; `lem-weil-pbc-etale-section-continuity` descends the finitely many degree-`q` section representatives and then the finitely many cocycle equalities to a later stage.
2. For injectivity, the same hypercover theorem represents a stagewise class. If its pullback is zero, `lem-weil-pbc-hypercover-refinement` supplies a finite-degree refinement and a primitive witnessing the boundary. The refinement, its map, primitive components, and the finite boundary equations descend by `lemma-weil-pbc-finite-hypercover-descent` and section continuity, so the class dies at a later stage. In degree zero, vanishing is directly section continuity.

No new `sorry` was introduced. The item remains dependent on the cited imported nodes, whose own proofs are separate work items.

The required Mathlib searches for this `none` Lean-audit item found no matching declaration: a natural-language LeanSearch query, a Loogle type-pattern query, and a recursive grep over Mathlib and the source checkout. The only related source declaration is the distinct fixed-scheme filtered-colimit theorem recorded above.

## Checks

- `python3 -m json.tool dag/nodes/sec-curve-estimates/lemma-weil-pbc-etale-cohomology-continuity.json`
- `python3 tools/review_split.py lemma-weil-pbc-etale-cohomology-continuity` (passes)
- `python3 tools/check_dag.py --cycles` (0 cycles; existing unrelated reach warnings only)

## Review by H1

I reviewed the submitted node against `coord/delivery-errors.md` A-F, the blueprint proof, and the four cited DAG statements. The item statement is unchanged and matches the blueprint node and Stacks Tag 03Q6 in hypotheses: a cofiltered inverse system of qcqs schemes with affine transitions, a torsion sheaf descended from one stage, and the canonical filtered-colimit comparison in every degree. The source-first search under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no exact declaration or matching `(blueprint: lemma-weil-pbc-etale-cohomology-continuity)` tag. The nearest source theorem, `Scheme.H_map_isColimit_of_isFiltered` at `AlgebraicGeometry/Curve/Reductions.lean:68-84`, is a different fixed-scheme filtered-colimit statement and contains `sorry`, so it is not an attachment.

The two proof steps follow the imported proof and are not relabellings. Step 1 uses `thm-weil-pbc-hypercover-cohomology` for finite-degree hypercover representatives, `lemma-weil-pbc-finite-hypercover-descent` for descent of the finite truncation and matching maps, and `lem-weil-pbc-etale-section-continuity` for descent of finitely many section components and the cocycle equation; these cited statements provide exactly those interfaces. Step 2 uses the same hypercover theorem for a stagewise representative and `lem-weil-pbc-hypercover-refinement` for a finite refinement and primitive witnessing a boundary; its `uses` now explicitly includes `lemma-weil-pbc-finite-hypercover-descent` and `lem-weil-pbc-etale-section-continuity` for descent of the refinement data and boundary equations. The degree-zero case is explicitly reduced to section continuity. Both steps are correctly marked non-elementary, and `proof_deps` is exactly the union of their `uses`; the previously listed `lemma-weil-pbc-fibre-product-limit` was removed because neither step invokes it.

The blueprint field was checked: the imported item keeps its own `blueprint.is`, has `same_as: []` after the whole-blueprint search, and the split report names the two blueprint proof paragraphs realized by the steps. No new nodes were created, so B1-B7 and C5 for new nodes are vacuous. No statement cites an uncarried Stacks tag, no cycle is introduced, and no hypotheses are added or dropped. The sandbox contains the item node at `dag/nodes/sec-curve-estimates/lemma-weil-pbc-etale-cohomology-continuity.json` and this report; no source checkout was written or built.

## Delivery summary

Files written: `dag/nodes/sec-curve-estimates/lemma-weil-pbc-etale-cohomology-continuity.json` (statement, no new nodes) and `report.md`.

Attachments: none.

WANTED: none.

Nothing was found wrong in the imported statement or blueprint route. The earlier imported dependency `lemma-weil-pbc-fibre-product-limit` was unused by both proof steps and was removed from `proof_deps`; step 2 now explicitly cites the two descent/section statements it uses.

Nothing remains unfinished in the split.
