# Stage-1 delivery: lem-weil-pbc-trivial-kan-homotopy-equivalence

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-trivial-kan-homotopy-equivalence.json`: statement, split; the existing statement is unchanged and its proof now has three steps.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-trivial-kan-lifts-monomorphisms.json`: statement of Stacks 08NM, Mathlib leaf via `SSet.rlp_monomorphisms`.

## Attachments

None. Searching the read-only slopmaster2 `WeilConjectures/` and `Comparator/` by item ID and by `trivial Kan` / homotopy-equivalence terminology found no declaration stating the item. Its audit is `none`.

## Wanted

None. The repository does not have its regenerated `literature/stacks-project/` directory, but I read the Stacks source `simplicial.tex` at `/home/ubuntu/c1-stacks-review/simplicial.tex` and checked the public pages for tags 08NS, 08NM and 019K.

## Corrections

The imported item had no proof, despite the Stacks source giving a short two-lift proof. I added the missing general lifting property as one Mathlib leaf. The statement itself and its unit route were not changed. The blueprint `from.place` was already precise; a search of the full blueprint for the trivial-Kan lifting and homotopy statements found no matching blueprint node, so `same_as` remains empty.

## Unfinished

None. No Lean was written or compiled at this stage.

## Review by E1

I read Stacks `simplicial.tex` Lemma 08NS (`lemma-trivial-kan-homotopy`, source lines 5641-5664) and Lemma 08NM (`lemma-trivial-kan`, lines 5550-5581), plus Definition 019K for the endpoint convention. The item has exactly the source's hypothesis of a trivial Kan fibration; its conclusion names a section and a homotopy that the source constructs. The new node states exactly 08NM: a boundary-lifting map lifts every square whose left map is injective in each degree. It introduces all four simplicial sets, the maps and the commutative square, and has no proof sketch or proof dependencies because it is a Mathlib leaf. `def-weil-pbc-trivial-kan-fibration` supplies the boundary-lifting notion and `def-weil-pbc-simplicial-set` supplies simplicial maps. I searched DAG nodes for 08NM, `lemma-trivial-kan`, degreewise injections and monomorphisms, and searched the whole blueprint with `blueprint_refs.py`; none states 08NM. I checked `CategoryWithFibrations.lean` lines 34-39 and 127-131: `I` is precisely the boundary-inclusion family, and `SSet.rlp_monomorphisms` is the equality needed to apply 08NM. Loogle found this declaration; LeanSearch returned HTTP 500; LeanFinder found only the related generating families. This is a direct Mathlib match once the established definition leaf identifies trivial Kan fibrations with `I.rlp`.

Step 1 applies the new leaf to the empty inclusion `empty -> Y`. The unique map out of the empty simplicial set makes the square commute, so the lift has `p o g = id_Y`; no nonempty-fibre hypothesis is silently used. Step 2 uses the existing simplicial-set and trivial-Kan definitions to identify the boundary of `Delta[1]` with its two constant vertices degreewise. Thus `partial Delta[1] x X -> Delta[1] x X` is injective in every degree. On the first endpoint the proposed top map is `id_X`; on the second it is `g o p`. The square commutes there because `p o g = id_Y` from step 1. These are pointwise identities and the defining product and boundary descriptions. Step 3 applies 08NM again to that square; the lift restricts to `id_X` and `g o p` on the endpoints, exactly a homotopy in Definition 019K. Along with the strict right-inverse equation, it is a homotopy inverse. Each non-elementary lifting assertion is cited by the new leaf; the remaining steps are endpoint and composition checks.

For small cases, when `Y` is empty the empty inclusion produces the unique section, and the cylinder square is still valid; when `X=Y=Delta[0]` and `p=id`, the section and homotopy are identities. Degree zero is covered by the empty-boundary inclusion in the Mathlib `I` family, as in the trivial-Kan definition's surjectivity clause. Degree one has two distinct constant endpoint simplices in every degree, so the map used in step 2 really is a degreewise injection. I found no source error or hidden hypothesis requiring a correction.
