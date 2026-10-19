# Stage-1 report: lem-trf-point-system-refine

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-system-refine.json` — statement, four proof steps, no new nodes, no Mathlib leaf.
- `citations.json` — verbatim citations for every node used by every proof step.

## Attachments

None. No sorry-free declaration for this item was found in the reference source trees.

## WANTED

None.

## What was wrong or incomplete

The imported item was unsplit. The Stacks proof of Tag 00YO says to “omit” the transition maps in the refined inverse system; the split writes them explicitly, including the mixed transition from a refined copy to an original copy and the pullback transition between refined copies. The source's use of the tail $J_{\ge j_0}$ and its cofinality is also stated explicitly. No statement correction was needed, and no source error was found.

I searched the whole DAG for the Tag 00YO statement, its key phrases, and likely filtered-colimit/refinement lemmas; the existing one-cover item was the only matching node. Blueprint searches for “one-cover refinement directed inverse system finite covering” and “preserving distinct sections factoring morphism through cover” returned no matching blueprint node. The required Mathlib searches for this item were run and logged: LeanFinder and LeanSearch returned only general filtered-colimit/site APIs, Loogle was unavailable because the proposed identifier was unknown, and grep found generic site/filtered-colimit declarations but no exact lemma.

## Review by Q30

I read the item node, its source location in `literature/stacks-project/sites.tex` (Tag 00YO and the proof context of Tag 00YP), the chapter `sec-trace-formula`, and unit `sk-i-curve-zero`. I also read the full statements of `def-weil-pbc-sites-and-cohomology`, `lem-weil-pbc-filtered-colimit-sets-elementwise`, and `lem-weil-pbc-filtered-colimits-commute-finite-limits`, which are the only cited nodes. Step 1 uses the filtered-colimit representation clause to choose $j_0$ and $f'$, uses the directed-poset tail argument, and uses the site's fibre-product/base-change covering axiom to form $V_{j,k}$. Step 2 uses exactly the site's sheaf equalizer injection and the existing Mathlib-backed finite-limit commutation node to pass the injection through the finite product and choose $k_0$; the empty-cover edge case is automatically impossible when $s\ne s'$. Step 3 verifies the new disjoint-union order is a directed poset and gives each transition map with its source and target; the pullback universal property gives the identity and composition laws. Step 4 checks that the refined summand is cofinal, so distinctness survives in the full colimit, and checks the factorization of the represented morphism through $W_{k_0}$. I tested the construction mentally on a singleton index, an already-factoring morphism, and an empty finite cover (the last has no compatible distinct sections). Every cited quote in `citations.json` is copied verbatim from its node statement.

## What could not be finished

Nothing; the server-side `check_dag` and `review_split` checks passed, and the required delivery dry run passed at commit `e8e3ddd17d`.
