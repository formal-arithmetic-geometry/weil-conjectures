# Source-first audit: lem-weil-pbc-sets-pushforward-stalk-strict-henselization

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-pushforward-stalk-strict-henselization.json`: repaired item, now split into four proof steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-etale-section-continuity.json`: new unsplit degree-zero continuity node for sheaves of sets.
- Deleted the returned auxiliary node `lem-weil-pbc-sets-strict-henselization-sections-colimit`; its content duplicated clause (2) of the item.

## Attachments

No exact sorry-free declaration was found for the item in `WeilConjectures/`. The nearby declaration `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` is for abelian sheaves and has a `sorry`, so it is not an attachment and is not used.

## WANTED

None. The Stacks source is present at `literature/stacks-project/etale-cohomology.tex`.

## What was wrong and what was repaired

The returned node `lem-weil-pbc-sets-strict-henselization-sections-colimit` restated the item's clause (2), so it was not a strictly smaller split. I deleted it and created the required general sheaves-of-sets continuity node. The item now reindexes the small cofiltered neighbourhood category by the directed-set theorem, applies the new continuity statement to the qcqs affine-transition system with the unit/composition/restriction maps, identifies components with restriction along `sigma_V`, and passes to the geometric stalk by cofinality. The old invalid affine-site section argument is contained in the new node's own affine-case proof route, not applied directly to non-affine `X_V`.

## Review by H1

I reread the item source, Stacks Etale Cohomology Tag 03Q9 (degree zero for sheaves of sets), including Tags 09YQ and 09YU. For the new node I read the affine-site/topos comparisons Tags 0EYL and 04HR and the sets section lemma 09YN, and checked that its statement introduces the directed system, sheaf, finite-presentation etale object, transition cocycle, and qcqs finite-affine-cover reduction. I also read `lem-weil-pbc-qcqs-morphism-permanence`, `lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-spec-small-colimit-limit`, `lem-weil-pbc-cofiltered-limit-directed-reindex`, `lem-weil-pbc-sets-etale-inverse-image-composition-units`, `def-weil-pbc-geometric-stalks`, and `lemma-weil-pbc-affine-neighbourhood-cofinal`.

For the new node I checked the affine case against Tags 04HR, 0EYL, 09YN and the existing site nodes, then checked the qcqs extension by finite affine covers, finite affine covers of pairwise overlaps, the sheaf equalizer, and commutation of finite limits of sets with filtered colimits. For step (a), I verified that the neighbourhood category is cofiltered rather than directed and that the reindexing node supplies the required cofinal directed family; its base changes are qcqs and have affine transitions. For step (b), I checked the continuity hypotheses with `W_0=X_{V_0}` and `G=pr_{V_0}^{-1}H`, the unit/composition/restriction transitions, and the restriction identification `(pr_V^{-1}H)(X_V)=H(X_V)`. For step (c), I checked both components of `sigma_V` and clauses (0)-(1) of the units node. For step (d), I checked that affine-neighbourhood cofinality and directed reindexing compute the same stalk colimit. The repaired JSON parses, every cited id exists, and the removed site-section citations no longer occur in the item steps.

I also checked edge cases: when the relevant fibre product is empty, both section sets have the unique empty-section value in the sheaf-of-sets convention; for a constant sheaf on an affine neighbourhood, the comparison reduces to the ordinary filtered colimit. The repaired JSON parses, every cited id exists in the repository, and no deleted node remains in the proof or dependency lists.

## What could not be finished

No Lean proof was written, as required for stage 1. The item remains a stage-1 split for the later proof stage.
