# Worker report: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system

## Review by J1

I read Stacks 00QV and 00QX against the item and six steps. Step 6 uses the fixed-ring module-colimit criterion with R = Z; the cofinal tail remains directed. Singleton and identity systems, empty presentations, zero generators/relations, and zero modules including s=t=0 were checked. Exact slopmaster2 searches found no attachment. A1-A7, B1-B8, C1-C8, D1-D5, and E1-E6 pass; cited nodes state each fact, the split is strict and acyclic, with no unrelated tool or file.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-limit-module-essentially-finite-presentation-over-system.json`: the existing worktree split has six proof steps following the 00QV ring construction and the 00QX module construction. This audit made no DAG edits.

## Attachments

None. I searched the read-only `slopmaster2` checkout at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact `(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system)` tag, the Stacks tags `00QV`, `00QX`, and `00R7`, and related finite-presentation, localization, directed-colimit, and module terminology. No declaration states the combined local-algebra and finitely-presented-module descent assertion. The nearest source results concern filtered colimits of localizations (`WeilConjectures/Mathlib/Algebra/Category/Ring/FilteredColimits.lean`) or scheme-level finite-presentation approximation; neither includes the node's module data and clauses (1)-(5). The node's `lean_audit.slopmaster2.state` is `none`. There is therefore no declaration to test against the sorry map or attach.

## Source and blueprint checks

I read [Stacks Algebra Lemma 00QV](https://stacks.math.columbia.edu/tag/00QV) and [Stacks Algebra Lemma 00QX](https://stacks.math.columbia.edu/tag/00QX) directly. 00QV constructs local rings by descending finite polynomial relations and contracting the prime; 00QX then descends a finite presentation matrix. Both omit their final verification. The item's hypothesis uses a *given* directed local-ring system with colimit `A`, whereas the source first chooses such a system. The node's clauses retain the source's ring and module colimit, essential finite type, finite module, ring localization, and module base-change conclusions; its final-stage base change is an additional explicit consequence of the same construction.

The six steps are: (1) descend the finite algebra presentation and inverse-image prime, citing the finite-presentation, essential-finite-type, localization-at-prime, localization-composition and elementwise-colimit nodes; (2) identify polynomial quotient base changes and the ring colimit, citing polynomial scalar extension, tensor quotient, ring-zero criterion, localization-colimit and cofinal-tail nodes; (3) identify ring transition and final maps as localizations, citing localization base change, localization composition, tensor quotient and localization-at-prime nodes; (4) descend the matrix and define cokernels with compatible semilinear maps, citing the elementwise-colimit and finite-module nodes; (5) prove both module base-change isomorphisms by right exactness of tensor, citing tensor-right-exact and module-base-change-universal-property; (6) prove the module colimit by lifting finite vectors and finite relations, citing the elementwise-colimit, ring-zero and module-colimit-criterion nodes, with the latter instantiated at the fixed scalar ring `Z` because the asserted colimit is in abelian groups. The node's `proof_deps` is the union of those cited `uses`.

For B9, `blueprint.same_as` is empty: this combined given-system assertion is a tool extracted from 00QV/00QX rather than a verbatim blueprint node. `blueprint.from` names `thm-weil-pbc-finite-etale-lifting`, its step 7, and the chain through `lem-weil-pbc-limit-tower-essentially-finite-presentation` and its approximation branch. Whole-blueprint searches recorded in `split_report.blueprint.same_as_search` found no same-statement node. The source text at `literature/stacks-project/algebra.tex` is absent in this checkout; the online Stacks pages supply the source comparison above.

## Checks and remaining work

`python3 tools/review_split.py lem-weil-pbc-limit-module-essentially-finite-presentation-over-system` passes with zero new nodes. `python3 tools/check_dag.py` reports zero cycles or self-loops; it exits nonzero for seven unrelated pre-existing unreachable nodes in the constructible-approximation branch. The current node is marked `split` and carries a prior `reviewed: 2026-10-10 L` field in the worktree. No Lean was written or built. No new node or Mathlib leaf resulted from this audit.

## Edge-case audit

The tail `Lambda_0 = {lambda >= lambda_0}` is nonempty (it contains `lambda_0`) and directed by directedness of `Lambda`; the same argument applies after each later common-stage choice. The construction permits zero generators or relations in the algebra presentation (`n = 0` or `m = 0`) and zero source or target rank in the module presentation (`s = 0` or `t = 0`); the polynomial, matrix, tensor, and cokernel arguments then specialize to the empty presentation and still give the asserted zero module or free module cases. In the module-colimit injectivity argument, a zero class is represented by a finite coefficient vector for the descended matrix; when that vector is empty, the equality is immediate, and otherwise the filtered-colimit zero criterion moves all finitely many coordinates to one later stage. The localization arguments use only that the inverse-image ideals are prime and that the displayed denominators avoid them, so they also cover a singleton index category and identity transition maps.
