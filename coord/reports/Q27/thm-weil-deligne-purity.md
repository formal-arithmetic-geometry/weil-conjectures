# Q27: thm-weil-deligne-purity

## Files written

- `dag/nodes/sec-zeta-weil/thm-weil-deligne-purity.json`: existing statement, seven-step split; no complete Mathlib match.
- `citations.json`: one literal statement passage for every step/node citation.
- `report.md`: this report.

## New nodes

None. Zero new nodes and zero Mathlib leaves. Searches before considering a new twist-weight or comparison-equivariance lemma found the existing lem-tw-tate-twist-weight-shift and lem-pod-proper-coincidence-frobenius; they are cited instead. No elementary computation or clause has been made into a new node.

## Attachments

None for this item. The searches for the exact blueprint tag and for purity/Frobenius in the read-only WeilConjectures source found no declaration giving all five clauses. `TraceDatum.isPureOfWeight_map_P_of_pairing` and `TraceDatum.norm_eq_of_mem_roots_charpoly_map_of_pairing`, WeilConjectures/ZetaLinearAlgebra/Purity.lean:63 and :131, assume the mixed weight bound and a perfect similitude pairing in an abstract TraceDatum. The module explicitly distinguishes this from the sheaf-theoretic clauses. These are not attachments of this item and are not used to bypass the weight theorem.

## WANTED

None. The current blueprint statement, proof, unit, and the statements of the existing DAG tools are available locally. The proof is marked agent-written because it repairs the agent-written blueprint argument rather than asserting a directly transcribed proof from an external paper. No SGA source is used.

## What was wrong and what changed

The imported two steps bundled unrelated clauses, used a twist definition as if it asserted the scalar-action theorem, and took Frobenius equivariance from a proper-coincidence statement that only asserts an isomorphism. The smooth-dualizing theorem also states an underlying duality identification, so its Weil equivariance needed a separate cited statement. These omissions are repaired with existing nodes: prop-weil-operations, lem-tw-tate-twist-weight-shift, and lem-pod-proper-coincidence-frobenius. The comparison calculation now writes the naturality and transport equations before composing them. The twist calculation is punctual, with each closed point's residue cardinality, so it does not incorrectly use q at all closed points.

The detailed main-20261015 statement agrees with the imported statement and is preserved verbatim. The broader unit summary explicitly dispenses with ambient exceptional-adjoint admissibility, whereas this detailed node still assumes it and a canonical dualizing lift and directly assumes finiteness. This is a source granularity mismatch, not a false hypothesis or an ill-typed statement; no counterexample to the conditional detailed statement is asserted, and no statement change is delivered. This detailed item is consequently not the full statement/key node of the broader unit: the latter also has the unconditional hypotheses, Q_l assertions, and the relative estimate. No unit realization edit is delivered, since doing so would incorrectly assert completion of that broader statement. The relative estimate already has its separate node thm-zl-wme-deligne-estimate. The current blueprint and DAG searches found no second blueprint node stating the full five-clause package; same_as is empty.

Three omitted statement notions are now explicit statement dependencies: algebraically closed coefficient category, complex weights, and Frobenius-module weights. All imported flags and blueprint provenance remain intact.

## What could not be finished

Nothing in the dispatched one-level split remains. Downstream imported theorem nodes are cited by their statements and left for their own items. No Lean was written or compiled.

## Not duplicates

No new nodes, hence no new/existing duplicate pairs. The smooth-proper corollary supplies only part of the five-clause package and is already its prescribed input; the constant-sheaf lemma supplies punctual purity, not the duality-defined lower complex-weight predicate. prop-weight-purity depends on this item and cannot serve as an input.

## Review by Q27

I read the main-20261015 item statement and its separate proof file, the sk-input-weights statement and proof, and the chapter and unit records. I also read the current full statements of every node cited in the seven steps; the passages in citations.json are copied from those statements. The proof follows the detailed source's smooth-duality/weight-estimate/smooth-proper-corollary route, with the missing mathematical interfaces exposed. There are no new nodes needing separate literature justifications or Mathlib verdicts. For the two generic calculations newly cited I read the main-20261015 Tate-twist statement and proof and the complete existing proper-comparison/Frobenius statement. The other inputs are exactly the source's existing DAG statements, not assertions extracted only from their proofs.

Step 1 uses lem-zl-constant-sheaf-weight-zero for punctual purity, def-weil-punctual-weights for the one-piece and empty filtrations, and def-weil-complex-weights for the degree convention. The scheme is separated finite type because it is proper over k_0. The distinction between punctual and duality-defined complex purity is maintained: this step proves only the upper predicate.

Step 2 checks the site-perfect hypothesis directly from def-weil-site-perfect-complex: the constant unit is free of rank one in degree zero at a finite field stage. The unit-dual computation is written explicitly using evaluation at 1 and multiplication; it is a short internal-Hom calculation, not a hidden theorem about arbitrary perfect complexes. def-weil-derived-pullback-tensor-hom supplies those operations and their common-stage interpretation. thm-sf-dual-perfect then supplies D_X K = K^vee(d)[2d], with smoothness, pure dimension and separated finite type checked. prop-weil-operations actually states that purity and duality isomorphisms are morphisms of Weil complexes; this is why it suffices to identify the canonical Weil lift in def-weil-complex-weights with the one fixed in the item. I do not infer Weil equivariance from thm-sf-dual-perfect alone.

Step 3 uses the full statement of lem-tw-tate-twist-weight-shift at w=0 and n=d; the constant sheaf is lisse of rank one and punctual purity is supplied by lem-zl-constant-sheaf-weight-zero. The lemma gives weight -2d at every closed point. The shift convention places the only nonzero sheaf in degree -2d, so its required weight is precisely j, not +2d. def-weil-punctual-weights gives the two filtrations and def-weil-complex-weights gives the lower predicate. This is the complete additional argument for complex purity; it does not cite prop-weight-purity, which would be circular.

Step 4 checks both finite-type and separated hypotheses of thm-zl-wme-deligne-estimate on a_X0 and applies its actual Rf_! statement, not merely a definition of mixedness. The cohomology identification uses def-weil-ordinary-compact-cohomology. The point's local operator has return degree one and equals the global operator by def-weil-local-frobenius-trace and the pushforward Weil structure of prop-weil-operations. Thus def-weil-punctual-weights on the point evaluates to the finite-dimensional module filtration of def-weil-frobenius-module-weights with q_y=q. No small-index colimit, unstated compact-support base change, or change of coefficient category is needed.

Step 5 separates the isomorphism from its equivariance. prop-weil-proper-compact-coincidence gives the former; lem-pod-proper-coincidence-frobenius gives the explicit transport equation for the same identity compactification. Its hypotheses include proper Y_0, which applies to X_0, and it permits Lambda=Q_lbar. Naturality with the Weil isomorphism theta supplies the second displayed equation in the step. Substitution of the two global Frobenius formulas from def-weil-global-geometric-frobenius proves commutation before taking cohomology. This repairs the most serious C4 gap in the imported proof.

Step 6 uses the statement of cor-zl-purity-smooth-proper, which supplies all integer degrees in the same Q_lbar coefficient category. Every geometric hypothesis is explicitly present in this item's assumptions; extra conditional assumptions in the item do not prevent applying it. It is the route's pre-existing smooth-proper input, not a newly invented node restating the whole package. Step 7 is the definition of Frobenius-module purity, quoted from def-weil-frobenius-module-weights, and is correctly marked elementary.

I checked the small cases d=0, i=0, the top degree i=2d, and vanishing cohomology groups. For d=0 the dualizing shift and twist are both zero. In top degree the lower-weight test still uses j=-2d on the dual complex; the global eigenvalue statement uses +d in the exponent, as required by geometric Frobenius on Q_lbar(-d). Zero sheaves and spaces use empty filtrations and have no eigenvalues, so no nonzero assumption is hidden. At a closed point of degree r the twist is controlled by q_y=q^r, which is why the old scalar-definition argument was replaced. No semisimplicity hypothesis was added.

I checked delivery-errors B–E: all new-node clauses are vacuous, every non-elementary input is a cited existing statement, the shorter formal calculations stay in proof steps, the cited nodes say what the steps use, coefficient categories and Frobenius conventions agree, and there is no restatement-node or proof-dependency cycle introduced by the split. Every step is under 2000 characters; step 2's unit-dual calculation and step 5's composition of two naturality equations are single routine calculations, fully written. Off-unit tools are declared individually in split_report.tool_uses with their purpose. The source has not been weakened and the unit route has not been replaced.

Mathlib searches were run only through msearch.py and are preserved in searches.jsonl. I read both LeanFinder result sets and the LeanSearch hits: they concern finite fields, smooth/etale algebras, condensed objects, affine limits and isocrystals rather than this theorem. The first grep had no hits; the second found only unrelated Deligne citations and archimedean gamma functions. Loogle reported unknown identifiers for the proposed project-specific purity/Frobenius names; this is recorded as its actual diagnostic, not an assertion that those services were unavailable. A second concept phrasing and the alternative regex were tried before recording no match.

## Delivery validation

The standalone server review_split passed. The first full dry run rejected a too-short literal proper-comparison formula; citations.json now quotes its full statement. A trial unit realization then caused check_dag to report that the unit did not reach its named Poincare-duality unit. I removed my trial unit edit: the detailed conditional item is not the full statement of that broader unit, so I cannot truthfully claim its complete realization or add an unused proof dependency simply to satisfy reachability. No shared unit metadata was changed. The delivered seven-step proof remains on the existing route and its actual citations are unchanged.
