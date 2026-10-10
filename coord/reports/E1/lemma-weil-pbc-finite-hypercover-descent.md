# Worker report: lemma-weil-pbc-finite-hypercover-descent

## Files written

- `dag/nodes/sec-curve-estimates/lemma-weil-pbc-finite-hypercover-descent.json`: split the existing statement into descent of the finite simplicial data, descent of its matching covers, and descent of morphisms and equalities. No new nodes.

## Sources and cited statements

The item's statement is the **Detailed form** in `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lemma-weil-pbc-finite-hypercover-descent.md`. Its earlier paragraph also asserts that an arbitrary hypercover admits a finite split refinement; that construction is not part of this item's Detailed form statement. The split follows the Detailed form proof. I read Stacks Project `limits.tex`, Lemma 01ZM (`lemma-descend-finite-presentation`), including its object, morphism, and equality clauses, and `etale-cohomology.tex`, Lemma 0EYL (`lemma-colimit-affine-sites`), including its finite-presentation and eventual-cover argument.

The statement of `lem-weil-pbc-etale-finite-data-descent` covers qcqs etale schemes of finite presentation, finite diagrams and their morphism equalities, and eventual descent of a finite covering family. The statement of the reviewed Mathlib leaf `lem-weil-pbc-etale-base-change-finite-limits` gives finite limits in the small etale site and preservation by base change. These are the facts used respectively in steps 1 and 3, and in step 2; the finite common-stage choice and finite coproduct bookkeeping are elementary consequences of the finite truncation in `def-weil-pbc-finite-split-hypercover`. The previous proof dependency `lemma-weil-pbc-fibre-product-limit` concerns a strict-henselization neighbourhood limit and does not state the finite-limit property needed here, so it was removed.

## Searches and attachments

The read-only slopmaster2 checkout `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` was searched by the node id, `hypercover`, `finite hypercover`, and descent terminology. It has no exact declaration for this item, so there is no attachment. `tools/blueprint_refs.py search 'finite hypercover'` and `search 'hypercover skeleta'`, together with a DAG text search, found this imported node and no duplicate statement to cite or create. The existing reviewed Mathlib leaf supplies the finite-limit fact; no new Mathlib-search verdict is needed for a new node because none was created.

## Edge checks and limits

For $r=0$, the matching object is $X$, so step 2 reduces to eventual descent of the degree-zero etale cover. If the limit is empty, the eventual-cover assertion still comes from the covering clause of `lem-weil-pbc-etale-finite-data-descent`; the proof does not assume a point of $X$. For a morphism or an equality, only finitely many components and compatibility equations occur through any fixed $r$, so the equality clause of that node applies at a common later stage. The split neither proves nor claims the earlier blueprint paragraph's finite-refinement existence; a citer needing that assertion must use a separate refinement result.

## Checks

`tools/review_split.py lemma-weil-pbc-finite-hypercover-descent` passes; `tools/blueprint_refs.py check lemma-weil-pbc-finite-hypercover-descent` reports zero field errors. The full `tools/check_dag.py` run reports seven unreachable-node and eleven route warnings from other nodes on the fetched base, with no cycle or diagnostic for this item. No `WANTED:` source and no unresolved item-specific issue.

## Review by E1

I read the imported blueprint statement and proof in this node's `blueprint_sketch`, Limits Lemma 01ZM (`lemma-descend-finite-presentation`, `limits.tex:2370`), and Etale Cohomology Lemma 0EYL (`lemma-colimit-affine-sites`, `etale-cohomology.tex:7336`). The delivered statement is the blueprint's Detailed form: descent of an already finite split truncation, its morphisms, and equalities. It does not include the preceding refinement-existence assertion. The hypotheses on the inverse system, finite presentation, and fixed finite degree match 01ZM and the qcqs case of 0EYL. No new node is created; B1-B10 and C5 on new statements are vacuous. I checked the existing `blueprint.is` and `blueprint.same_as` and the refreshed `lean_audit` against origin; they are retained.

Step 1 uses the finite nondegenerate-component description in `def-weil-pbc-finite-split-hypercover` and the object, morphism, equality, and finite-diagram clauses actually stated by `lem-weil-pbc-etale-finite-data-descent`. The common stage and finite coproduct assembly are finite bookkeeping. Step 2 uses `lem-weil-pbc-etale-base-change-finite-limits` for matching objects and the covering clause of the finite-data node for the descended matching maps. Finite limits of the lower-degree etale finite-presentation terms remain etale of finite presentation; thus the covering clause applies to these matching schemes. Step 3 again uses the morphism and equality clauses of the finite-data node; only finitely many equations arise at fixed degree. The removed strict-henselization fibre-product citation did not state the needed fact. The steps carry the proof rather than restating the result in a helper, and the dependency graph has no new cycle.

For E1-E5, I checked that every application occurs over the same eventual stage and fixed finite truncation, that the target matching schemes are within the small etale site, and that no infinite family of identities is silently descended. At degree zero the matching map is the augmentation to `X`; an empty limit scheme still uses the cited eventual-cover clause; the morphism/equality assertion only involves finite component data. I sent the missing-report defect back to the worker, who added this report in the repaired commit; no mathematical change was requested. Section A is checked by preflight after the current-tip rebase.
