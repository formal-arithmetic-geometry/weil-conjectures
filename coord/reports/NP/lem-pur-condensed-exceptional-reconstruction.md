# Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-condensed-exceptional-reconstruction.json` — retained the existing ten-step statement split; no new nodes; Mathlib searches are retained with their recorded no-match verdicts.
- `citations.json` — verbatim statement citations for every proof-step dependency.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its exceptional-reconstruction terminology, and the boundedConstructibleUpperShriek declarations. No sorry-free declaration states this item, and no declaration carries the blueprint tag.

WANTED: `literature/upstream-master-20261016/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean`, lines 100–156, for the exact master definitions of the chosen bounded-constructible exceptional right adjoint; that archival path is absent from this checkout. The report relies on the available blueprint and the archived source path named in the item node.

The item and its existing split were copied from the shared DAG after checking the current repository version. I searched the DAG and blueprint for exceptional-reconstruction, normalized semilinear tower, adic reconstruction, and condensed upper-shriek formulations. Existing reconstruction and realization nodes are cited where their statements are used; no additional node is created because the item proof is the required argument and its auxiliary facts are already represented by existing nodes. The target statement, hypotheses, coefficient categories, chosen compactification right adjoint, and unit/shift clause were retained unchanged.

## Review by NP

I read the item node, `sec-smooth-purity.json`, the `sk-thm-purity-transport` unit record, and the current `main-20261015` blueprint proofs for `sk-prop-sp-integral-adjunction`, `sk-prop-sp-rational`, `sk-thm-sp-qbar`, and `sk-prop-sp-unique-adjoint`. I also opened the statement of every dependency cited by each of the ten steps; the accompanying `citations.json` records the exact statement text used for each citation.

Step 1 establishes a uniform Tor-amplitude interval from the stratified-perfect models, finite pro-etale refinements, K-flatness, and open-closed assembly. I checked the qcqs/noetherian and finite-dimensional hypotheses and the invertibility of ℓ, and verified that each cited node states the local model, stalk detection, tensor-pullback, open-closed, K-flat, and derived-change-of-rings facts that this step invokes. The empty and zero-object cases are explicitly covered.

Step 2 forms the finite-level normalized exceptional system using the finite-coefficient adjunction comparison, semilinear sections, and the cartesian-section adjoint-mate theorem. I checked that the cited statements provide the coherent quotient maps, invertible mates, section adjunction, and counit; the step does not use an unstated ambient adjoint.

Step 3 treats the two alternatives in the hypothesis. For the single-degree case I checked the good-truncation construction, componentwise cohomology identification, and shifted full-faithfulness citations, including naturality and transport of the geometric counit. The stronger enhanced identification in case (a) is used exactly as supplied.

Step 4 checks the displayed chain of derived Hom complexes. The compact-support realization node supplies the comparison with the chosen functor, the evaluation calculus supplies the limit/mapping identities, the section-mate node supplies the middle adjunction, and the bounded-complete definition supplies the final completeness isomorphism. I verified that H⁰ is taken only after the chain and that the resulting counit reduces to the finite-level counits.

Step 5 checks rationalization: tensoring the integral Hom bijections with E, applying the realization equivalence and compact-support comparison, and using existence of lattices. The rational-category and rational-transport statements say precisely these operations and do not assume a finite-field or algebraically closed base.

Steps 6–7 check finite coefficient-field extension and cofinal quotient descent. I verified the finite-free completed-scalar, constructibility, finite-level exceptional-mate, semilinear-section, condensed realization, and flat-coefficient statements supply the claimed identifications, quotient cocycles, counits, and compatibility for every pair of levels and every ramification index.

Step 8 uses the two-colimit statement to descend an arbitrary Ω-object to a finite coefficient field and to identify eventual equality of morphisms. I checked that the compact-support realization comparison is the only additional input and that the argument covers arbitrary finite-stage test objects.

Step 9 applies the uniqueness-of-adjoint/Yoneda transpose to obtain the natural condensed comparison and its counit. I checked the compactification-refinement compatibility and that the chosen right adjoint is the one explicitly defined in the item statement.

Step 10 checks the unit and shift clauses directly from the realization equivalence and flat coefficient calculus. I tested the edge cases f=id, empty X or Y, L=0, degree r=0 and r≠0, equal coefficient fields, and ramified finite extensions. No hypotheses are silently added, no SGA source is used, and no step cites a proof detail absent from its dependency statement.

## Not duplicates

No new node was created. The existing normalized-witness and compact-support-realization nodes are used for distinct auxiliary statements; neither restates the full exceptional-reconstruction conclusion of this item.

## Source error / limitations

The source path recorded in the imported node is unavailable in this checkout, so the exact UpperShriek source exhibit cannot be independently reopened here; this is reported above as WANTED. The available blueprint and dependency statements support the retained proof route.

What remains unfinished: no Lean work or compilation is authorized in stage 1, and none was performed.
