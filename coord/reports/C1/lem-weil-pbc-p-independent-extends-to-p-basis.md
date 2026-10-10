# Worker report: lem-weil-pbc-p-independent-extends-to-p-basis

## Files

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-p-independent-extends-to-p-basis.json`: existing uncommitted six-step split inspected and preserved. No new nodes.

## Attachments

None. Search of the read-only `WeilConjectures/` tree at `/home/ubuntu/weil-src-slopmaster2` found neither `(blueprint: lem-weil-pbc-p-independent-extends-to-p-basis)` nor a p-independence or p-basis declaration. Thus there is no Lean declaration to compare with the sorry map for this item.

## Sources and checks

Read `more-algebra.tex` in `/tmp/c1-lead-current/literature/stacks-project/`: `definition-p-basis` at line 11344 (tag 07P1) and `lemma-p-basis` at line 11363 (tag 07P2), with both mappings confirmed in `tags/tags` lines 9781-9782. The definition is monomial independence and spanning over `kK^p`; the lemma says every p-independent collection extends to a p-basis. The draft's six steps expand its Zorn proof at lines 11401-11409: remove duplicate indices, check chains, identify the monomial span with the generated subfield, prove an element outside it has degree p, contradict maximality, and reindex the resulting basis.

The only cited non-elementary facts are `lem-weil-pbc-zorn-lemma` (its statement gives a maximal member when every chain is bounded), `def-weil-algebraic-element` (the root of `X^p-x^p` is algebraic), and `lem-weil-pbc-simple-algebraic-extension-power-basis` (powers through degree minus one are a basis). The remaining calculations, including the empty initial family and characteristic two, are explicit in the steps. Whole-blueprint search by p-independence and 07P2 found no equivalent imported node. The split adds none, so new-node checks do not apply.

`python3 tools/review_split.py lem-weil-pbc-p-independent-extends-to-p-basis` passes. `python3 tools/check_dag.py --cycles` reports zero cycles and seven reachability warnings for unrelated constructible nodes.

## Source error

Line 11408 prints `L(x) = L[z]/(z^p - x)` while assuming `x` lies outside `L`; its right side is undefined as an `L`-algebra because `x` is not a coefficient in `L`. For example, with `K=F_p(t)`, `k=F_p`, `L=F_p(t^p)` and `x=t`, the printed polynomial is not in `L[z]`. The corrected polynomial is `z^p - x^p`, since `x^p` is in `L`, and the draft's degree argument proves the needed independence. The item statement is unchanged.

## Unfinished

## Review by C1

I read More on Algebra 07P1 (`definition-p-basis`) and 07P2 (`lemma-p-basis`) in local `more-algebra.tex`. The item retains exactly the extension of a p-independent family to a p-basis. Step 1 turns the indexed family into a subset and checks duplicate entries violate independence. Step 2 verifies upper bounds for chains and cites Zorn for a maximal set. Step 3 shows the monomial span is a field. Step 4 cites the simple-extension power-basis node and proves the degree of x outside the span is p; its shifted-polynomial calculation fills the source's omitted argument. Step 5 groups relations by powers of x to contradict maximality. Step 6 reindexes the basis. The cited nodes state the facts used. I checked empty initial family, duplicate indices, p=2, and x outside the monomial span.

The source's displayed `L[z]/(z^p-x)` is ill-typed because x is not in L; with K=F_p(t), L=F_p(t^p), x=t, the coefficient x lies outside L. The proof uses `z^p-x^p`, whose coefficient lies in L. The item statement is unchanged. The worker re-read local TeX and corrected its source note. Searches of the current DAG, imported blueprint, Mathlib and read-only slopmaster2 found no exact existing declaration. No child was created. `review_split.py` passes; `check_dag.py` has no cycles and seven unrelated reach warnings. Sections A-E of `coord/delivery-errors.md` are satisfied. The source error is recorded for L to relay in `coord/HUMAN.md`.

No mathematical gap identified. Lead review and delivery remain.
