## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-comparison-global-cohomology.json`: split item.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-derived-sections-pushforward.json`: one new unsplit statement node; Mathlib searches found no match.

## Attachments

None. The slopmaster2 declaration `isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj` is only a degreewise vanishing result and does not state this natural derived isomorphism.

## WANTED:

None.

## What was checked

The item and its proof were checked against the blueprint file `lem-weil-pbc-comparison-global-cohomology.md`. Existing statements of `prop-weil-pbc-site-comparison-finite-level`, `def-weil-pbc-site-comparison-morphism`, and `thm-weil-pbc-site-comparison` were opened and used only for exactness, the comparison adjunction, and the derived-unit isomorphism they actually state. The new node records the intermediate identity obtained by resolving a bounded-below pro-etale complex by injectives and evaluating the right derived pushforward on the final object. Its statement is strictly more general than the item and is not a restatement.

Step 1 cites the finite-level exactness proposition, the comparison morphism definition, and the new derived-sections statement; these supply exactness, the right adjoint, and the natural derived-sections identity respectively. Step 2 cites that identity and the bounded-below full-faithfulness theorem, then substitutes `J = ν_T^*K` and applies derived global sections. I checked the finite coefficient and bounded-below hypotheses at both steps. I also ran LeanFinder, Loogle, grep, and LeanSearch searches for the new node; LeanSearch was unavailable and recorded as such. No existing DAG node or blueprint node states the new identity.

## Review by NE

I read the source blueprint proof and the full statements of all four cited existing nodes. The finite-level proposition explicitly states exactness of `ν_T^*`; the comparison-morphism definition explicitly supplies the adjunction and `ν_{T,*}`; and the site-comparison theorem explicitly states the bounded-below derived-unit isomorphism. The new node supplies only the missing derived-sections calculation, so the item’s two steps together reproduce the source argument without moving the item’s conclusion into a duplicate node. The empty and bounded-below cases are covered by the stated resolution hypothesis; no stronger coefficient or site hypothesis was introduced. I corrected the imported dependency list by adding the comparison-morphism definition to the item’s statement dependencies and by replacing the un-cited paragraph proof with a two-step proof whose uses match the node statements.

## What could not be finished

No Lean code or compiler was run, per the stage-1 restriction.

## Second reading by NE

- Item statement: read the blueprint node and checked the finite-coefficient and bounded-below hypotheses; added the explicitly missing hypothesis that $T$ is a scheme so the statement is self-contained.
- New node `lem-weil-pbc-derived-sections-pushforward`: checked its scheme, finite-ring, site-morphism, bounded-below-complex, and ordinary-derived-sections clauses against the comparison proof paragraph; verdict self-contained and strictly auxiliary to the item.
- Step 1: read the statements of `prop-weil-pbc-site-comparison-finite-level`, `def-weil-pbc-site-comparison-morphism`, and the new node; exactness, adjunction, and the derived-sections identity supply precisely the uses claimed, with no unlisted hypothesis.
- Step 2: read the new node and `thm-weil-pbc-site-comparison`; bounded-belowness is preserved by $\nu_T^*$ and the derived-unit isomorphism gives the displayed conclusion by applying derived sections.
- Edge cases checked: zero complexes and the zero finite ring make both sides zero; a field coefficient ring introduces no extra assumption; bounded-below complexes include degree-zero complexes.
- New-node audit: searched the imported DAG, blueprint, and Mathlib search log for an existing derived-sections identity; none matched. The recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches are retained.
- Changes: made the item statement self-contained by adding “For a scheme $T$”; no proof step or citation needed alteration. Dry-run preflight passed after this repair.
