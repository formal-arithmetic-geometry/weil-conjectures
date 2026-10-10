# Worker report: `lem-weil-pbc-simplicial-set-add-simplices`

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-set-add-simplices.json`: split into four proof steps; no new nodes.

## Attachments

None. The refreshed `lean_audit.slopmaster2` state is `none`. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-src-slopmaster2/Comparator` by the item id, blueprint tags, and the notions `simplicial set`, `nondegenerate`, and `add simplices`; no exact sorry-free declaration exists.

## Source and proof

The proof follows Stacks Project `simplicial.tex`, Lemma 018S (`lemma-add-simplices`), with its hypotheses and one-simplex conditions from Lemma 018R (`lemma-glue-simplex`). It inducts on the finite number of nondegenerate simplices of `V` outside `U`: choose a least-dimensional missing nondegenerate simplex `x`, adjoin all its degeneracies, verify closure under every simplicial operator by factoring an ordinal map as a surjection followed by an injection, and recurse. The formerly implicit finite-ancestor, closure, finiteness, and induction details are written explicitly in the four steps.

## Mathlib search

The existing item searches remain recorded: LeanSearch (`SSet.Finite`, `SSet.Subcomplex.le_iff_contains_nonDegenerate`), LeanFinder (`SSet.modelCategoryQuillen.J_le_monomorphisms`, `I_le_monomorphisms`), and a Mathlib grep of the simplicial skeleton API (`SSet.skeletonOfMono`, `SSet.relativeCellComplexOfMono`). They do not state the required one-simplex chain; Mathlib attaches all simplices of one dimension at once, which is not a one-line specialization.

## Checks

`python3 -m json.tool`, `git diff --check`, `tools/review_split.py` (PASS, zero new nodes), and `tools/blueprint_refs.py check` (zero errors) pass. Global `tools/check_dag.py` reports seven unreachable-node and eleven route diagnostics in unrelated nodes; no diagnostic concerns this item. No source checkout was written or built.

## Unfinished

Nothing.

## Review by E1

I read `simplicial.tex` Lemma 018S (`lemma-add-simplices`), Lemma 018R (`lemma-glue-simplex`), and Definition 0175 (`definition-terminology-simplicial-sets`), together with the sandbox item and the cited `def-weil-pbc-simplicial-set` statement. The item's inclusion, finite nonempty degree sets, and finite nondegenerate-simplex hypotheses are exactly those of 018S; its three conditions reproduce 018R(1)-(3). The current `lean_audit.slopmaster2` is `none`, and the read-only source search found no exact declaration.

A: the sandbox contains this item's node and report only; packaging, current-base preservation, one-commit shape, and preflight are checked by the delivery command. B: there are no new nodes. C: step 1 uses only the cited definition's degeneracy notion and closure of a simplicial subset; decreasing dimensions terminate. Step 2 uses that ancestor argument and least missing dimension. Step 3 uses the cited functorial simplicial operators and subset closure; every finite-ordinal map factors as a surjection followed by an injection, and a surjection has an order-preserving section, as the text explains. These elementary order facts are enough for the closure, the three 018R conditions, and the assertion that degeneracy in V remains degeneracy in W. Step 4 applies ordinary finite induction with the hypotheses verified in step 3. No step takes an unstated theorem from a cited node or introduces a dependency cycle.

D: the item retains its conclusion and supplies the construction and induction that 018S leaves terse; it does not move the conclusion into another node. E: for zero missing nondegenerate simplices, step 1 gives U=V and the empty chain. For the first missing simplex in degree zero, the lower-degree condition is vacuous; the construction still adds only x in degree zero. For positive degree, minimality puts every proper face in U. Nonemptiness of U ensures every intermediate W is nonempty in each degree, and inclusion in V ensures finiteness. I found no extra hypothesis in any step. I checked the four steps against the cited definition and Stacks 018S/018R and found no mathematical correction needed.
