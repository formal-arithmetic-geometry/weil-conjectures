# Stage-1 report: lem-trf-site-inverse-image-composition-generators

## Files written

- `dag/nodes/sec-six-functors/lem-trf-site-inverse-image-composition-generators.json`: statement node, split into five proof steps; no new nodes and no Mathlib leaf created.
- `citations.json`: verbatim quotes for every node used by every proof step.
- `report.md`: this report.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, its title, and the relevant sheaf-composition names; no sorry-free project declaration states this exact arbitrary-site generator normalization and equality-detection assertion.

## WANTED

None. The cited Stacks sources are present in `literature/stacks-project/`.

## Existing-node and statement checks

The item statement was retained exactly. Its source is `literature/stacks-project/sites.tex`, Tag 03CB, with the colimit construction from Tags 00VE and 00WX. I searched the whole DAG and blueprint for site inverse-image composition, nested colimit generators, and Tag 03CB. `lem-weil-pbc-site-morphism-composition` is a broader site-composition result only under exactness hypotheses; it does not state this item's weaker hypotheses or generator formula. `lem-weil-pbc-sets-inverse-image-composition` is for topological spaces, and `lem-weil-pbc-sets-etale-inverse-image-composition-units` is specifically for small etale scheme sites. `lem-trf-constant-coefficient-composition` is a ring-sheaf specialization. None is a duplicate, so no new node was required.

The item’s existing Mathlib searches were read and retained: grep, Loogle, LeanSearch, and LeanFinder searches on sheaf-pullback composition all found only generic sheafification/pushforward or over-category results and no declaration of the nested generator formula with equality detection. The item remains a non-Mathlib statement node.

## Review by Q56

I read the item source and the full statements of every cited node: `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`, `def-weil-pbc-sheafification`, `def-weil-pbc-composite-adjunction`, `lem-weil-pbc-conjugate-iso-unit-equation`, and `lem-weil-pbc-adjunct-counit-identity`. I also read the local Stacks passages for Tags 00VE, 00WX, and 03CB, and Categories Tag 0B65.

Step 1 uses the adjunction node for the hypothesis that precomposition sends sheaves to sheaves, the colimit formula for `u_p`, and the sheafified left adjoint for each of `u`, `v`, and `uv`; it uses the sheafification definition for the universal map in each coprojection. The direct-image equality is the literal equality of precomposition functors, so the source and target of all three adjunctions are the stated sheaf categories.

Step 2 uses the composite-adjunction node for the unit `v^s(eta^u) eta^v`, and the conjugate-isomorphism node with the identity right-adjoint comparison. I checked that the direction is `u_s v_s -> (uv)_s` and that its unit equation is exactly the displayed compatibility in the item.

Step 3 evaluates that unit equation on `x` and arrows `psi` and `phi`. The cited adjunction node supplies the two colimit coprojections and the composite colimit; the sheafification node supplies the universal map after each colimit; and the conjugate node supplies the unit-compatible comparison. The resulting arrow is exactly `u(psi) phi`, with the stated order. This computation does not assume a single representative for an arbitrary sheafified section.

Step 4 uses the composite hom-bijection and the adjunct/counit identity to reduce equality of two maps to equality of their adjuncts. The adjuncts agree on every section of every object because the composite unit is precisely the nested generator from Step 3. I checked that this works in both sets and abelian groups and that componentwise equality of natural transformations is the required conclusion.

Step 5 records naturality in the sheaf and in restriction arrows. This follows from the functoriality explicitly stated in the adjunction node, the universal sheafification map, and naturality in the conjugate-isomorphism node. All five proof steps are under 2000 characters, so no hidden long sublemma remains. `proof_deps` is exactly the union of the listed `uses`, and every citation quote in `citations.json` is a verbatim substring of its node statement.

I tested the statement conceptually on identity functors, an empty site, and a one-object site: the comparison is the identity-compatible map and the generator test reduces to equality on ordinary sections. I also checked that the item’s hypotheses do not assert exactness, so the exactness-dependent site-composition node was not cited.

## What was wrong or changed

The imported node had an empty proof and status `unsplit`. I supplied the complete five-step proof and set status to `split`; the statement, dependencies, blueprint ancestry, and existing Mathlib-search records were preserved. No statement correction or source discrepancy was found.

## What remains unfinished

Nothing within this stage-1 item. The maintainer’s review and global landing remain downstream of delivery.
