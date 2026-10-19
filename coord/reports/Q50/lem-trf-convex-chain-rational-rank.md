# Stage 1 report: lem-trf-convex-chain-rational-rank

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-convex-chain-rational-rank.json`: repaired item with the cardinal-dimension citation in Step 4.
- `dag/nodes/sec-trace-formula/lem-trf-torsionfree-rationalization-injective.json`: existing statement-only auxiliary node retained.
- `dag/nodes/sec-trace-formula/lem-trf-independent-family-cardinal-dimension.json`: restored reviewer-added Mathlib leaf, with exact declaration and source lines.
- `citations.json`: verbatim citations for all non-elementary step dependencies.

## Attachments

None. No finished project declaration states this item in the available source trees.

## WANTED

- `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, §2.1 pp. 7–8, for the source discussion of convex rank and the height consequence. The local archive does not contain this PDF; the ordered-group proof is marked agent-written while following the cited route.

## Source error

The imported finite-range conclusion conflicted with `def-trf-rational-rank`, whose dimension is cardinal-valued. The item therefore uses `Cardinal.mk (Fin n) ≤ rrk Γ`. The returned landing also exposed a missing C1 dependency: the independent-family cardinal bound is a separate Mathlib fact, so the reviewer-added Mathlib leaf `lem-trf-independent-family-cardinal-dimension` is restored and cited in Step 4.

## Review by Q50

I reread the corrected item and every cited node: `def-trf-rational-rank`, `lem-trf-torsionfree-rationalization-injective`, and the restored `lem-trf-independent-family-cardinal-dimension`. Step 1 uses only strict subgroup inclusion and total order to choose positive representatives. Step 2 uses torsion-freeness of an ordered abelian group and the definition of convexity. Step 3 cites exactly the torsion-free rationalization statement, which gives injectivity of `G → G ⊗ ℚ`; the largest-index coefficient argument is written explicitly. Step 4 cites exactly the restored Mathlib leaf, whose statement gives the cardinal bound for any linearly independent family in an arbitrary-dimensional vector space, and combines it with the rational-rank definition. I verified every hypothesis: no endpoint condition on the chain, no finite-dimensionality assumption, and cardinal-valued dimension throughout.

For the restored Mathlib leaf I read `Mathlib/LinearAlgebra/Dimension/Basic.lean` lines 84–101, including `LinearIndependent.cardinal_lift_le_rank` and `cardinal_le_rank`, and `Dimension/StrongRankCondition.lean` lines 367–370 for basis-cardinality identification. Its searches were run with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch; the exact records are retained in `searches.jsonl`. The item searches likewise remain recorded. The new leaf is a Mathlib status node with no proof, as required.

I checked edge cases `n=0`, rank zero, `\mathbb Z`, lexicographic `\mathbb Z^2`, and uncountable direct sums. No cited node is duplicated: the rationalization node states tensor-map injectivity, while the restored leaf states the independent-family/cardinal-dimension inequality. The proof steps are all below the long-step threshold.

## Not duplicates

- `lem-trf-torsionfree-rationalization-injective` vs `lem-trf-convex-chain-rational-rank`: tensor-map injectivity for torsion-free groups versus the convex-subgroup chain bound.
- `lem-trf-independent-family-cardinal-dimension` vs `lem-trf-convex-chain-rational-rank`: the Mathlib leaf bounds an arbitrary independent family by ambient cardinal dimension; the item constructs such a family from a convex chain.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-birational-quasi-modification`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines birational quasi-modifications. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-centred-valuation`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines centred valuations. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-modification`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines scheme modifications. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-multipointed-curve-modification`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines modifications of multipointed curves. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-multipointed-curve`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines multipointed curves. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-multipointed-eta-modification`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines eta-modifications of multipointed curves. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-nodal-dualizing-datum`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines nodal dualizing data. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-schematically-dense-open`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines schematically dense opens. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-semistable-multipointed-curve`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines semistable multipointed curves. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-torsionfree-rationalization-injective` vs `def-trf-semistable-multipointed-pair`: the new node states injectivity into rationalization for a torsion-free abelian group; the existing node defines semistable multipointed pairs. The shared 0707 string is the arXiv filename, not a common Stacks theorem.
- `lem-trf-independent-family-cardinal-dimension` vs `lem-weil-independent-family-card-le-dimension`: the existing statement assumes the ambient vector space finite-dimensional, whereas the restored leaf permits arbitrary cardinal dimension.
- `lem-trf-independent-family-cardinal-dimension` vs `lem-weil-dimension-span-independent-family`: the existing statement computes the finite span dimension, whereas the restored leaf bounds the family by ambient cardinal dimension.

## Repair of landing 8c81b809b4

The reviewed fixes existed only in the independent review packet and were absent from the retained worker sandbox. This repair adopts both reviewer fixes into the worker delivery: the explicit convexity definition and Step 4 citation, and the independent-family Mathlib leaf. The leaf has empty proof and proof dependencies, null proof origin, an explicit field definition dependency, and actual Mathlib matches; its created.by is now worker because this delivery adopts it as a worker-created Mathlib leaf, rather than passing it as an unsplit reviewer-added node through the landing-only fix interface. The delivery command rebases owned fields onto current main. Current main retains the same item ancestry; the rational-rank definition still gives cardinal dimension. No change to a target or another worker node is made.

STATEMENT-DISPUTED (retained correction): the original natural-number-or-infinity range excludes the uncountable rational rank of an uncountable lexicographically ordered direct sum of copies of Z. The cardinal inequality repairs that type mismatch without changing the intended finite-chain bound.
