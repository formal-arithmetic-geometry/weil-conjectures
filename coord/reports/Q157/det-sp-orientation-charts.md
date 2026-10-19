# Stage-1 report: det-sp-orientation-charts

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-orientation-charts.json`: existing item split and reviewed for delivery; no new nodes.
- `citations.json`: 57 verbatim step-to-node statement quotes.
- `searches.jsonl`: Mathlib searches run by `msearch.py`.

## Attachments

No sorry-free project declaration states the full chart orientation comparison. The source search covered `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures`; only component declarations for affine-line orientation and diagonal constructions were found, with no declaration tagged `(blueprint: det-sp-orientation-charts)`.

## WANTED

None. The blueprint proof and all cited statements are present in the repository.

## Statement and source review

The item statement is the finite-coefficient chart comparison from `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-charts.md`; its expanded proof follows `sk-prop-sp-orientation-charts.proof.md`. I retained the imported statement and made its hypotheses explicit: finite-type schemes over the algebraic closure, separated finite-type smooth `f` of pure dimension, open `U`, and an étale coordinate map. I checked that the conclusion uses the specified exceptional inverse image, derived pullback, Tate twist, diagonal orientation, and ordered affine coordinate adjunction. The statement does not assume absolute separatedness of `Y`, matching the blueprint.

The unit and chapter records read were `dag/units/sk-prop-sp-orientation.json` and `dag/chapters/sec-smooth-purity.json`. The nearest blueprint ancestor is `det-sp-orientation-charts`; the imported item has `blueprint.is` equal to its id and `blueprint.from: null`, with `same_as: []`. The existing item’s imported proof has no new nodes and its proof dependencies all exist in the current DAG.

STATEMENT-DISPUTED (inherited source-domain omission, already repaired in the current item): read without the standing chapter hypotheses, the blueprint introduces only a smooth morphism. But `def-weil-exceptional-inverse-image` defines the displayed constructible `Rf^!` only for separated finite-type morphisms between finite-type $k$-schemes. Thus that unrestricted reading is outside the functor's stated domain; likewise the diagonal need not be closed without relative separatedness. I retain the existing explicit domain correction, justified by the unit's own sentence “Since $f$ is separated” and by the finite-coefficient conventions. This delivery makes no further change to the item statement, and it imposes no absolute separatedness on $Y$.

## Review by Q157

I read every cited dependency statement before retaining the split and generated one verbatim quote for every step/dependency pair in `citations.json`. Step 1 uses the finite-type/Noetherian, open-subscheme, quasi-compact-open, affine, separated-base-change, smooth-dimension, and affine-space-smooth statements to restrict to affine target opens and verify the separated finite-type DNC domain. Step 2 uses the definition of separatedness, closed-immersion base-change permanence, quasi-compactness, and the étale definition to prove the chart is separated and finite type. Step 3 uses étale base change, the clopen diagonal, and smooth relative-dimension permanence to construct the Cartesian neighbourhood of the diagonal. Step 4 uses diagonal regular immersion, flat conormal base change, the affine flat criterion and tensor exactness, the conormal graded algebra, and relative Spec to identify normal bundles and their zero sections; the degree-by-degree calculation is written explicitly. Step 5 uses cohomological smoothness, étale locality, diagonal base change, ordinary étale adjoint locality, Nagata compactification, and mate pasting to identify the source maps and section invariants. Step 6 uses the normalized DNC invariance theorem and section-geometry statement; the coordinate normalization removes any residual scalar. Step 7 uses vector-bundle purity, coefficient-twist base change, vector integration comparison, and linear trace invariance to identify the final arrows. Step 8 multiplies the three displayed identities and applies `det-sp-orientation-vector-bundle` and `lem-pur-projection-purity-agreement`; this is an elementary composition once those statements are cited. Step 9 uses smooth/DNC/vector-bundle base change, affine-space trace base change, mate pasting, derived-single full faithfulness, pro-étale localization, and sheaf Hom gluing to descend equality from affine opens and checks the empty and `d=0` cases.

I checked the two mechanically long steps (Step 4, 2041 characters; Step 9, 2119 characters). Step 4 is one degree-by-degree flat graded-algebra calculation followed by relative Spec, with every algebraic input cited; it does not hide a separate lemma. Step 9 is one locality and equality-detection argument, with the sheaf full-faithfulness and gluing statements cited; its final edge cases are explicit. I also tested a non-injective étale chart: for two disjoint copies of $A$ mapping to $A$, $U\times_AU$ has off-diagonal components, which Step 3 removes; this confirms that using the full inverse image as the diagonal would fail. No clause is restated as a new node, no duplicate node was created, and no cycle or route replacement was introduced. The existing review correction adding `lem-pod-separated-finite-type-base-change` to Step 3 is retained. The source route uses the allowed lecture-notes/Stacks path and cites no SGA 4 or SGA 4½.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## What was corrected

The imported proof’s domain localization and relative-separatedness checks were retained. I reconciled all 11 Mathlib search records against the existing `msearch.py` log without repeating them. The initial LeanSearch rate limit and the two Loogle unknown-identifier errors have verdict `unavailable`; the successful retries and both semantic phrasings are retained. Preliminary grep queries with redundant Mathlib path prefixes are explicitly superseded by the corrected subdirectory and whole-tree searches. Every recorded tool and query is copied from the log. The item remains `status: split` with the existing maintainer metadata untouched.

## Unfinished

Nothing in the item split remains unfinished.
