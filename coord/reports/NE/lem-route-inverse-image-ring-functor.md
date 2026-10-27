## Files written

- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-ring-functor.json`: statement node, completed four-step proof; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim citations for every non-elementary node use in every proof step.

## Attachments

None. No declaration in the project source or slopmaster2 states this item exactly.

## WANTED

None.

## What was wrong or incomplete

The live item was unsplit: it had the correct statement and dependencies but no proof. The two cited prerequisite nodes already provide the needed smaller results, so creating another ring-object or sheaf-algebraic-structure node would have duplicated existing DAG statements. I kept the statement unchanged and transported those results across the existing sheaf/ring-object isomorphisms. The item’s pre-existing Mathlib search records were retained, and four fresh searches (LeanFinder, Loogle, grep, LeanSearch) were run and appended; they found only partial sheafification/module or internal-ring APIs, not this theorem.

## Review by NE

I read the live item, `dag/units/sk-thm-rationality.json`, `dag/chapters/sec-zeta-weil.json`, the blueprint construction sentence for `sk-thm-rationality`, and the complete statements of both cited nodes. Step 1 uses exactly the statement of `lem-weil-pbc-sheaf-algebraic-structures-objects`: on each site, commutative-ring sheaves are isomorphic to internal commutative-ring objects and the isomorphism commutes with underlying sheaves. Step 2 uses exactly `lem-weil-pbc-adjunction-lifts-group-ring-objects`: from the assumed finite-product-preserving adjoint pair it supplies the ring-object functors, their underlying functor equalities, operation transport, and the lifted adjunction. Step 3 checks that these data can be transported through the two categorical isomorphisms; the component of the underlying functor equality is the required `e_R`, its naturality is the naturality of that equality, and the operation equations are precisely the finite-product/terminal comparisons stated by the cited lift. Step 4 uses the lifted hom-equivalence and the same isomorphisms to recover the original set-sheaf hom-equivalence, units, counits, ring naturality, and all operation clauses. The only hypotheses used are the two small-site/sheaf-category setup assumptions and finite-limit preservation of `L`; the right-adjoint finite-product preservation needed internally is supplied by the cited lifted-adjunction theorem. I checked the empty site, identity adjunction, and zero-ring cases conceptually; all constructions reduce to the canonical terminal/product comparisons. The required server `check_dag` preflight passed after the final citation repair.
