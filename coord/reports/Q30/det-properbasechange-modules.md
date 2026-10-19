# Stage-1 report: det-properbasechange-modules

## Files written

- `dag/nodes/sec-proper-base-change/det-properbasechange-modules.json`: split item; no new nodes.
- `citations.json`: verbatim citations for both proof steps.
- `report.md`: this review and delivery report.

## Attachments

None. The Lean source contains no sorry-free declaration tagged `(blueprint: det-properbasechange-modules)` or stating the complete item. The existing declaration `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` proves the abelian/module proper-base-change theorem in a different formulation and does not state the coefficient-forgetting identification required here.

## WANTED:

None.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs. The existing `lem-weil-pbc-module-abelian-derived-exchange-compatibility` is a supporting compatibility theorem: it states the fixed coefficient comparisons and the equality of the module and abelian derived exchange maps, while this item additionally packages that equality as `For(Ex^Λ)=Ex^Z` and derives the torsion isomorphism consequence.

## What was checked and corrected

The imported item and its blueprint proof were read in `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/sk-thm-properbasechange-modules.md` and its `.proof.md` companion. The target statement was retained. Its original two proof paragraphs were audited against the DAG. The first paragraph cites a coefficient-comparison result that already exists as `lem-weil-pbc-module-abelian-derived-exchange-compatibility`; I use that node directly instead of recreating its resolution and coefficient-cube argument. The second paragraph uses `thm-weil-pbc-bounded-below`, whose statement was read in full and supplies properness, Cartesianity, bounded-below input, and torsion cohomology. The remaining assertion that forgetting module structure is exact and conservative is elementary from the module-sheaf definitions: kernels and cokernels are computed on underlying abelian sheaves, and quasi-isomorphisms are therefore reflected.

For Step 1, I checked that the cited node states the exact source and target comparison isomorphisms (`s_K` and `r_K`) and the equality of the forgotten module exchange with the abelian exchange, for every bounded-below module complex and the canonical `derivedBaseChangeMapPlus` transformations. For Step 2, I checked every hypothesis of `thm-weil-pbc-bounded-below` against the item: the square is Cartesian, `f` is proper, and `For K` has torsion cohomology. I also checked the small coefficient case `Λ = ℤ/nℤ`, where the torsion hypothesis is automatic, and the identity-square case, where the conclusion reduces to the identity exchange map.

Mathlib searches were run through `msearch.py` for LeanFinder, LeanSearch, Loogle, and source grep in two phrasings. They found only generic sheaf-forgetting and derived-category infrastructure; no exact proper-base-change compatibility theorem. The exact queries and verdicts are recorded in the node's `mathlib_searches` field.

## Review by Q30

I read the target source, both blueprint files, `lem-weil-pbc-module-abelian-derived-exchange-compatibility`, and `thm-weil-pbc-bounded-below`. Step 1 takes exactly the coefficient comparison and exchange equality stated by the former node; its hypotheses cover a commutative square and an arbitrary bounded-below module complex, so the item's Cartesian square and `K` fit. Step 2 takes exactly the proper Cartesian torsion base-change isomorphism stated by the latter node; all three hypotheses were checked against the item's assumptions. I verified that the first proof step does not silently identify coefficient categories: it uses the explicit fixed `For`, `s_K`, and `r_K` comparisons from the cited statement. I verified that the second step's reflection claim is the elementary underlying-sheaf fact and does not require a new node. I corrected the imported proof by replacing its long unsupported resolution argument with the existing precise compatibility node, and I made the off-unit use explicit in `split_report.tool_uses`. I checked the item on the zero/identity square and on finite torsion coefficient rings before finalizing the split.

## What could not be finished

Nothing. The split is complete and ready for the required dry run.

## Second reading by Q30

- Item statement: read the current blueprint `sk-thm-properbasechange-modules.md` and its proof, the defining nodes for derived exchange, coefficient categories and Cartesian squares, and `det-pbc-conventions-module-cohomology`. The commutative ring, proper f, arbitrary g, chosen Cartesian square and bounded-below K agree; torsion is needed only for the consequence. The statement is unchanged and needs no dispute.
- Step 1: read the full statements of the original compatibility citation and the stronger existing `lem-weil-pbc-exchange-forget-coefficients`. The latter clauses (1)–(3) state exactly the canonical comparisons and exchange equality, for any Cartesian square and bounded-below module complex. Read Stacks `sites-cohomology.tex`, Lemma 0D6J (`lemma-modules-abelian-unbounded`, part (3)) and Remark 07A7 (`remark-base-change`), plus Lemma 03FD (`lemma-cohomology-modules-abelian-agree`) for the conventions. Verdict: use the existing same-unit exchange-forgetting theorem; no assumption that forgetting preserves injectives is made.
- Step 2: read `thm-weil-pbc-bounded-below` in full and Stacks `etale-cohomology.tex`, Lemma 0DDE (`lemma-proper-base-change`). The given square is Cartesian, f is proper, and For K is bounded below by the exact/cohomology comparison in the exchange-forgetting node; its cohomology is torsion by the item's added assumption. That node's final equivalence supplies reflection of invertibility. Verdict: both facts are cited explicitly, and `elementary` is false; no uncited derived conservativity argument remains.
- New nodes: none (zero Mathlib leaves). No elementary lemma or duplicated clause was introduced. Whole-blueprint search for `properbasechange modules` returned this imported item only. DAG tag/key-word searches found the existing exchange-forgetting node, which belongs to the same unit and depends on neither this item nor proper torsion base change.
- Edge cases: K = 0 gives the unique invertible map between zero objects; the zero coefficient ring has only zero modules; an identity square gives identity exchange under the canonical comparisons; an empty source gives zero direct images. For a field of positive characteristic, and for Z/nZ with n > 0 (including n = 1), every module is additively torsion. For a characteristic-zero field the identification still holds, but the torsion consequence requires its stated hypothesis. No dimension or nonemptiness assumption was added.
- Independent searches: reran LeanFinder with `forgetful functor reflects isomorphisms derived category module sheaves` (eight generic underived reflection results), Loogle with `Functor.reflects_iso derived category sheaf modules` (query rejected: unknown constant), and grep with `proper base change module coefficients forget` (zero hits). The actual outputs are in `searches.jsonl`; no rejected query is treated as evidence of absence. Read the slopmaster2 proper-base-change declaration: it states the torsion consequence, not the coefficient-forgetting identification, so no finished declaration states this whole item.

Changes made in this second reading:

- Replaced the lower-level off-unit compatibility citation with the existing same-unit exchange-forgetting theorem, which also supplies exactness, the cohomology comparison and reflection of invertibility.
- Replaced the unsupported elementary reflection assertion in Step 2 by the theorem's stated equivalence and explicitly checked boundedness of For K.
- Removed the obsolete off-unit tool-use request, updated `proof_deps` and `split_report`, and regenerated all three step citations from the exact existing node statements.
- Corrected the first search's result names to its actual log, recorded the independent searches, and marked rejected Loogle queries as rejected rather than negative searches.

The first worker's report and `## Review by Q30` above are preserved as required; this section records the repaired final proof.
