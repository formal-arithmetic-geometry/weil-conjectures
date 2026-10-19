# Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-of-cospan-limits.json` — statement node, split with five proof steps, no new nodes and no Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited dependency in every proof step.
- `report.md` — this report.

Attachments: none. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` found no declaration tagged `(blueprint: lem-coef-infinity-equivalence-of-cospan-limits)` or stating this theorem without `sorry`.

WANTED: archived Kerodon source for Proposition 6.3.5.3 (01N7), especially the cospan-limit comparison used in its proof. The live Kerodon page was read and its functor-core comparison is at lines 77–94.

The imported statement is unchanged. The seeded route was sufficient after adding the existing test-core criterion as a proof dependency; no new DAG node was needed. Mathlib searches found only ordinary-category `IsLimit`/walking-cospan declarations, which do not state the coherent infinity-categorical result.

## Review by NN

I read the item node, the `sec-six-functors` chapter record, and the `sk-prop-sf-biduality-general` unit record. I also read the complete statements of `def-cbc-enhanced-diagrams-cones`, `lem-coef-cat-infinity-colimits-cartesian-closure`, `lem-coef-infinity-pointwise-equivalences`, `lem-coef-infinity-terminal-pullback-criterion`, and `lem-coef-infinity-test-equivalence-by-functor-cores`; each citation in `citations.json` is a verbatim substring of the cited statement. The source is Kerodon Proposition 6.3.5.3 (01N7), whose proof compares the functor-core cospan square and then tests it against every infinity category.

Step 1 fixes an arbitrary small test quasicategory (Q), uses the internal coherent functor construction, and uses the pointwise-equivalence statement to turn the objectwise cospan equivalence into equivalences on all three functor-core vertices. The cartesian-closure statement supplies natural coherent postcomposition and the enhanced-diagram definition supplies quasi-inverses and inverse coherences. I checked that this step uses component equivalences only and does not assume strict inverses.

Step 2 applies the terminal-pullback criterion separately to the two specified limiting cones in 
\(\mathrm{Cat}_\infty\). Its displayed comparison has exactly the three mapping spaces of the cospan and retains the given cone coherence, so the hypotheses “both cones are limiting” and “(Q) small” are used at this step.

Step 3 checks the compatible cone map makes the two comparisons commute. The terminal-pullback statement explicitly gives naturality in maps of cones and invariance under equivalences of cospan diagrams; Step 1 supplies the three equivalences. No strictification of the coherent square is introduced.

Step 4 is the one-line two-out-of-three argument for equivalences of spaces in the commutative comparison square. It produces the required postcomposition equivalence for every (Q), including the empty or terminal test shape.

Step 5 invokes the existing all-test-core criterion to obtain the apex functor equivalence. Conversely, the quasi-inverse and coherent inverse transformations in the definition of functor equivalence postcompose to inverse maps on every coherent functor quasicategory and its core; the cartesian-closure naturality verifies this is the stated all-(Q) condition. Thus the “equivalently” clause is proved in both directions.

I tested the statement on the degenerate cospan (all three objects equal), on a cospan with an empty or terminal apex, on (Q=\Delta^0), and on (Q=\varnothing); the argument still uses only the same homotopy-pullback comparisons. The Mathlib search log records both phrasings for LeanFinder, Loogle, grep, and LeanSearch. Loogle and grep gave no applicable infinity-categorical declaration; LeanFinder and LeanSearch returned only ordinary-category cospan/limit results, so `mathlib_match` remains null. The blueprint ancestry and supporting-cell-gluing place were retained, and no source or statement correction was required.
