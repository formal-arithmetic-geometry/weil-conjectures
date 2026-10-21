# Stage-1 report: lem-sfb-scalar-coordinate-limit-criterion

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-scalar-coordinate-limit-criterion.json`: existing statement, now split into seven proof steps; not a Mathlib leaf. Statement and its four statement dependencies are unchanged. All earlier citations and searches are retained, and six actual Q77 searches are appended.
- `citations.json`: eight entries, one for each step/node citation, copied verbatim from the current cited statements.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record, Lean file, repository file, or launcher file was written.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, scalar-coordinate and finite-power language, restriction of scalars, and internal-module limit declarations. The project has internal-module forgetful limit constructions and preservation results, but no declaration states this entire criterion. Ordinary ModuleCat restriction results and the generic cancellation lemma do not by themselves prove the internal-module claim.

## WANTED

None.

## Audit of the imported item and route

The item was statement-only, with no proof. I read the current chapter and unit records, their third step, and the current `lem-sfb-subfield-flat.proof.md`. Its final sentence passes from a natural finite-power description to exactness. This item realizes precisely the finite-limit part of that inference; it makes no assertion about cokernels or infinite limits. There is no change to the statement, coefficient categories, chapter route, or unit route, and no STATEMENT-DISPUTED issue.

The proof uses existing DAG tools instead of adding nodes for standard module limits, conservative reflection, or cancellation. In particular `lem-sfb-modobj-restriction-finite-exact` would not give reflection, and an ordinary ModuleCat result alone would change the category. The actual proof uses the existing equivalence that explicitly preserves internal modules' underlying abelian sheaves and sections. No additional closedness hypothesis, flatness hypothesis, point of the site, or nonzero rank assumption is introduced.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. Whole-DAG statement searches for finite powers, preservation/reflection/creation of limits, restriction of scalars, and the two Mathlib declaration names identified the existing tools used here. Whole-blueprint searches (`blueprint_refs.py search`) for finite limits, reflects, products preserve, finite power, coordinates, and restriction of scalars found no blueprint node stating this criterion. The nearest ancestor is `lem-sfb-subfield-flat`; the existing exact final-sentence provenance is retained and `same_as` is empty.

## Review by Q77

I read the worker brief, the stage-1 contract, SETUP's three-level rule, GOAL, and both copies of delivery-errors B through E. For the item's source I read the actual final paragraph of `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`. It supplies the intended route, not the missing scalar-restriction argument. I therefore mark the expanded proof as agent-written. I also read Stacks `sites-modules.tex`, lemma-limits-colimits (03DB), including the componentwise limit-action construction, and lemma-limits-colimits-abelian-sheaves (03CO). I inspected the cited equivalence node and its 00YV algebraic-structures reference; I rely on the equivalence node's explicit statement for the internal/sectionwise comparison, rather than claiming that 00YV alone states that comparison. No new node requires a new source.

For step 1, I opened `def-weil-pbc-internal-abelian-sheaf-module-equivalence` and `lem-weil-pbc-module-sheaves-limits-sectionwise`. The first really asserts an equivalence for commutative internal rings with the sheafified abelian tensor and identical underlying sheaves and sections. The second really asserts limits as compatible families, with componentwise action, sheaf property, universal projections, and sectionwise computation. The item supplies the equivalence's size, sheafification and monoidal-equivalence hypotheses, separately for R and B. Finite index categories fit the coefficient universe, so no oversized limit is taken. The equivalence transfers these universal properties by its bijections on morphisms; no sectionwise equivalence of a different coefficient theory is assumed.

For step 2, I opened `def-sfb-modobj-restriction`: its action is gamma composed with phi tensor the identity and its underlying arrows and objects are unchanged. Together with the sectionwise-limit node this gives precisely r acting on a compatible family by (phi(r) x_j)_j, so the restricted canonical cone is the canonical R-module cone. The argument for an arbitrary limit cone writes out why applying the functor retains the inverse maps of its unique isomorphism with that cone. This is an elementary consequence of the two cited constructions, not a new restriction-exactness lemma.

For step 3, I checked `sk-def-sfb-module-objects`' actual linearity equation and its definition of composition, and the same restriction node. An inverse to Vf yields an inverse of the underlying sheaf morphism. The displayed calculation proves B-linearity of that inverse using f's B-linearity and the two inverse identities; it does not infer B-linearity just from R-linearity. Both sides have domain B tensor N and codomain M. No tensor preservation of monomorphisms or limits is used.

For step 4, I read the full statement of `lem-sfb-conservative-left-exact-reflects-finite-limits` and pinned Mathlib `CategoryTheory/Limits/Preserves/Finite.lean:175-178`. Its three hypotheses are exactly source finite-limit existence (step 1), preservation (step 2), and reflection of isomorphisms (step 3). It supplies reflection of cones, not merely reflection of terminal objects. This is already a Mathlib leaf in the DAG.

For step 5, I checked the actual universal-property construction: coordinate projection of a cone to D(j)^n is a cone over D; each gives a unique map into L; the n-tuple gives the desired map into L^n. The two uniqueness properties give uniqueness without any exactness theorem or choice of sections. This is a direct product/limit calculation, so I left it as an elementary step. For n=0 all target powers are terminal. For the empty J, L is terminal and its finite product is terminal by the same unique-map argument. In particular neither exclusion n>0 nor nonemptiness of J is hidden.

For step 6, I checked alpha's direction and naturality: the cone maps are postcomposed with alpha at D(j), the lift is precomposed with alpha_L inverse, and F(p_j) alpha_L inverse equals alpha_D(j) inverse P_n(p_j). The written uniqueness argument works when there are no legs. Thus this is explicit transport of the preceding universal property, not an uncited natural-isomorphism preservation theorem.

For step 7, I opened `lem-sfb-finite-limit-preservation-cancellation` and Mathlib `CategoryTheory/Limits/Preserves/Finite.lean:163-166`. It needs preservation by the composite and reflection by the second functor and no additional existence/additivity hypotheses. Steps 6 and 4 give exactly these hypotheses with F=T. It concludes preservation of the original T-cone, including the empty diagram, as the item requests.

The statement was tested on n=0, n=1, the empty diagram, the empty site, zero coefficient rings, and a noninjective ring morphism. The proof never cancels phi or assumes a basis: only the supplied alpha matters. I checked that all non-elementary external assertions occur in cited node statements and every citation has its verbatim record. All seven steps are below 2000 characters; the coordinate and inverse calculations are elementary consequences of the displayed definitions and universal properties, not hidden new lemmas. No statement or source correction was needed. The only off-unit non-leaf tool is the internal/sectionwise equivalence, explicitly declared in `split_report.tool_uses`; the remaining non-definition tools are Mathlib leaves. New-node B1/B2/B5/B6 gates are vacuous, and I have not relabelled a clause of the item as a new node (D1/D2).

The six Q77 Mathlib queries in `searches.jsonl` all returned successfully: LeanSearch, two LeanFinder phrasings, Loogle, and two greps. I read the results and checked the actual source of the cancellation/reflection matches, sectionwise limits, the internal comap definition, and ModuleCat's flat-extension result. The last requires a flat ordinary ring map and states a different category-specific result; none is a one-line match to this criterion. All retained inherited searches are clearly inherited and unchanged; every appended query was actually run. No searches were fabricated or failures recorded as absence.

## Unfinished work

No mathematical work remains for this one-level split.

## Validation

The required `deliver.py Q77 lem-sfb-scalar-coordinate-limit-criterion --no-push` exited 0 and printed `OK (not pushed)` at f4cf9fdf704: server preflight passed. The push command performs its own final delivery checks.
