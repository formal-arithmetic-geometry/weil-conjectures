# Stage 1 delivery: `def-sc-constant-sheaves`

## Files written

- `dag/nodes/sec-curve-estimates/def-sc-constant-sheaves.json` - split the imported definition without creating a new node.
- `coord/reports/C1/def-sc-constant-sheaves.md` - this worker report.

## Source and statement

The item is the imported blueprint definition at `sec-curve-estimates/sk-prop-cd/def-sc-constant-sheaves.md`, order 1007. Its text defines `F_n` as the sheafification of the constant presheaf with value `Z/nZ` and asserts that each geometric stalk has that value. The blueprint markdown is absent from this worktree, so I checked the imported text in the node and the corresponding unit and chapter records. The unit `sk-prop-cd` uses constant coefficients in its cohomological-dimension argument; this item only supplies their definition.

The definition now cites `def-sc-curves` for its base scheme, `def-weil-pbc-etale-sheaves` for the small etale site, and the verified Mathlib leaf `def-weil-pbc-constant-sheaf` for the sheafification construction. Its geometric-stalk clause is retained and supported by the existing `lem-weil-pbc-constant-sheaf-geometric-stalk`, whose statement applies to any constant abelian etale sheaf. No proof step is hidden in this definition and no new node is needed.

## Lean and blueprint searches

The refreshed `lean_audit.slopmaster2.state` of the item is `none`. Searches in read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` found no `def-sc-constant-sheaves` tag or exact declaration for the whole item. `AlgebraicGeometry.Etale.constantModSheaf` at `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/Defs.lean:94` defines a related constant sheaf with value `Lambda/dLambda` over an arbitrary coefficient ring. It does not state the geometric-stalk clause, so it is not an attachment. The source's `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso` at `WeilConjectures/Mathlib/CategoryTheory/Sites/Point/ConstantSheaf.lean:82` is a related stalk isomorphism; its application to the specific map in the existing DAG stalk theorem is a bridge, not an exact attachment to this definition.

LeanSearch and Loogle found `CategoryTheory.constantSheaf`. The Mathlib source at `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean:66` defines it as the constant-presheaf functor followed by sheafification, matching the construction here on `C` with value `ZMod n`. The existing DAG node `def-weil-pbc-constant-sheaf` already records that Mathlib leaf. Searching the imported blueprint for "constant sheaf" also found `def-constructible-constant` and `def-kun-constant-sheaf`; each covers a broader setting and neither states this item's combined curve-specific definition and stalk clause. Hence `blueprint.same_as` is `[]`.

## Edge cases and dependencies

For `n = 1`, `Z/nZ` is zero and the stalk theorem gives zero stalks. On an empty curve the sheaf construction still exists and the stalk claim has no points to check. On a disconnected curve it is the same constant-presheaf sheafification on the whole site; the stalk theorem applies at each geometric point without connectedness. These cases require no prime or smoothness assumption. The existing stalk theorem depends on the general constant-sheaf definition, not on this item, so the added dependency introduces no cycle.

## Attachments

None. The related Lean declarations above do not state this entire item exactly.

## WANTED

None for this one-level definition split. The blueprint markdown is not present on this machine; its imported text is in the node file.

## Follow-up noted

`thm-sc-main` step 1 cites this item for the geometric-stalk assertion. The assertion is retained, so that citation remains valid. The underlying proof is now visible as `lem-weil-pbc-constant-sheaf-geometric-stalk`.

## What could not be finished

Nothing within this item. No Lean was written or built.

## Review by C1

I compared the revised item with its imported blueprint sentence at order 1007 and the `sk-prop-cd` unit record; the blueprint markdown itself is absent here. The definition still says that `F_n` is the sheafification of the constant presheaf with value `Z/nZ` on the small etale site of a curve, and still asserts that its geometric stalks have that value. I opened Mathlib `CategoryTheory/Sites/ConstantSheaf.lean:66`, which defines `constantSheaf` by constant presheaf followed by sheafification, and the statement of `def-weil-pbc-constant-sheaf`, which says the same in the DAG. I also opened `def-sc-curves` and `def-weil-pbc-etale-sheaves`; they provide exactly the curve and site used here.

For the stalk clause, I opened `lem-weil-pbc-constant-sheaf-geometric-stalk`: it gives the canonical isomorphism from any abelian group `E` to the geometric stalk of its constant etale sheaf. Taking `E = Z/nZ` yields this item's clause, with no connectedness or smoothness hypothesis. That lemma depends on the general constant-sheaf construction, not this curve-specific item, so the citation is noncircular. `thm-sc-main` cites this item for the stalk clause; I sent the worker back after its first version moved that clause to a pointer and would have broken the citation. The worker restored the clause and changed `blueprint.same_as` to `[]` after checking that the other constant-sheaf nodes are broader, not identical.

There are no proof steps or new nodes, so the citation-by-step and new-node checks B-D have no instances. The read-only slopmaster2 search found a related constant-module-sheaf construction but no exact declaration including this item and its stalk assertion. At `n = 1` both value and stalk are the zero group; on an empty curve the stalk claim is vacuous, and disconnected curves require no extra case. I checked the final item and report against delivery-errors A-F, including the corrected downstream citation.
