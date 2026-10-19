# Q68: thm-pod-trace-isomorphism

## Files written

- `dag/nodes/sec-poincare-duality/thm-pod-trace-isomorphism.json`: statement node, split into six steps, no Mathlib match after two phrasings and source grep.
- `citations.json`: one exact statement excerpt for each of the twenty step/node citations.
- `searches.jsonl`: the search command's unmodified log. The item's `mathlib_searches` records the same tools and query strings, with the rejected first Loogle query marked unavailable.

No new DAG nodes, Mathlib leaves, definitions, Lean files, or unit records were created. Sandbox-only preparation scripts are not DAG deliveries.

## Attachments

None. I searched the project Lean source by the blueprint id and by trace/cohomology terminology. `AlgebraicGeometry.WeilSheaf.traceIsomorphism_adicConstant`, `WeilConjectures/WeilSheaf/TraceIsomorphism.lean:306`, has a sorry-free body, but it is not an attachment for this item. It asserts existential linear equivalences only at `PadicAlgCl l`; the module's implementation notes explicitly say that neither the named canonical trace on Weil complexes nor the E stage is stated. The DAG requires both field stages and identification with the orientation-counit map. Moreover its proof uses `poincareDuality_compactlySupportedCohomology_adicConstant`, which uses the explicitly sorried `exists_isPerfPair_compactlySupportedCohomology_adicConstant` at line 111. I did not rewrite or seed maintainer-owned Lean audit fields.

## WANTED

None. The item follows the available current blueprint. No new external-source lemma is introduced.

## What was wrong

**STATEMENT-DISPUTED (coefficient typing, repaired).** The imported and current-blueprint statement names `cor-pur-finite-stage-smooth-dualizing-complex` as supplying the orientation at Lambda = E or Qlbar. Its current, reviewed statement fixes Lambda = A_{E,n}; its displayed orientation has target A_X(d)[2d]. Substituting Lambda = E into that declaration is outside its domain: E is a characteristic-zero field while A_{E,n} is killed by a power of ell, so these coefficient objects cannot be identified. This is a source-reference type error, not a false trace theorem. I replaced the reference by `cor-pur-adic-and-rational-smooth-dualizing-complexes`, explicitly retaining the finite orientation as the starting point of its transport. The corrected field-stage orientation and counit are exactly those already fixed in `def-pod-conventions`. Every conclusion, coefficient stage and geometric hypothesis is retained. The current blueprint's removal of the obsolete numbered Definition 1.49 reference is also adopted.

The imported proof additionally used the twist definition for the scalar q^{-d}; that definition now expressly delegates the scalar theorem to `lem-pur-twist-frobenius-scalar`. It claimed Frobenius compatibility from `cor-cbc-proper-coincidence`, whose statement concerns a finite-coefficient base-change exchange and does not assert the required operator identity at the field stages. Finally, the connectedness proposition is stated at E, so applying it at Qlbar without a common-stage argument was a gap. The split repairs each of these without a new node.

The proof does not apply `def-weil-poincare-trace-cup` alone to a nonproper X: that older definition fixes properness and Q_l. It always uses the explicit all-coefficient, compact-support reading `def-pod-trace-cup-reading`. Likewise it does not apply the finite-only smooth-trace definition at E directly: the field-stage trace is its transported version in the smooth-dualizing-complex corollary and in the equivariance theorem.

## What could not be finished

Nothing in the one-level split. The cited existing nodes keep their current states; this delivery does not claim that they have been proved in Lean.

## Not duplicates

No new nodes. I searched the whole imported blueprint for trace and constant coefficients, read the matches, and reused the existing constant-coefficient corollary, coefficient-scalar theorem and proper-Frobenius lemma. `cor-pod-constant-coefficients` includes the trace isomorphisms but not the item's Frobenius assertions; `sk-cor-trace` includes point-class normalization and other coefficient stages but does not state this exact nonproper field-stage theorem. Neither is recorded as an equivalent blueprint statement, so `same_as` is empty.

## Review by Q68

I read `coord/brief-stage1.md`, stage 1, the three blueprint levels in SETUP, delivery-errors B through E, GOAL, and the DAG-sync rule. I read the chapter record, the `sk-cor-trace` unit and its current `_section.md`, and both the imported item and its `blueprint_update`. The proof source is the complete current `main-20261015/.../sk-cor-trace/thm-pod-trace-isomorphism.proof.md`, read alongside its statement and the current constant-coefficient corollary. The proof remains agent-authored, as that blueprint is agent-authored. I read every statement cited below, not merely its proof or dependency list. There are no new nodes with further sources to audit.

Step 1 uses the actual setting in `def-pod-conventions`: smooth, separated finite type, geometrically connected of dimension d, with no properness. I checked the full finite-stage smooth-dualizing-complex statement and the current field-stage corollary (also its main-20261015 `sk-cor-sp-all-coefficients` text). Only the latter supplies the orientation at E and Qlbar and identifies its counit with normalized integration. The trace reading identifies precisely that map and its untwisting. This repairs the coefficient typing above rather than silently identifying coefficient categories.

Step 2 takes only the connectedness clause of `prop-cohomological-finiteness`, whose statement explicitly removes properness and smoothness for H^0. I checked that its coefficient is E, not Qlbar. For the latter I read `prop-weil-pbc-descent-functors` (its explicit ordinary-direct-image clause), the definitions of ordinary cohomology and point fibre (clause 4), and `def-weil-point-fd-qlbar-category` (cohomology after a transition is H^i tensor L). Together these represent ordinary cohomology at a common finite stage. The common-stage operator convention is explicitly in `def-pod-conventions`. The equations E tensor_E L = L and id tensor 1 = id show the conclusion at every later stage; no proper scalar-extension lemma was used on a nonproper scheme.

Step 3 uses the statement of `cor-pod-constant-coefficients`, not an argument hidden in its proof. That statement provides the top-degree isomorphisms at both field stages, explicitly says the first is induced by the trace, and imposes no properness. The displayed evaluation-at-1 argument records why this is the actual map identified in Step 1 rather than an arbitrary choice of a linear equivalence. The second map is the untwisted trace by the trace reading. No new node repeats an existing clause.

Step 4 uses the full current statement of `thm-pur-weil-equivariance-of-purity-and-trace`. I verified its separated finite-type descent over k_0, smooth geometric fibre, dimension and coefficient hypotheses for the structure morphism. The point coefficient unit is free rank one in degree zero, hence has Tor amplitude [0,0]; it is a valid K. The theorem explicitly supplies the normalized-smooth-trace square at both field stages. Applying point fibre and cohomology uses precisely the operators defined in `def-pod-conventions`; the m=0 case of `lem-pur-twist-frobenius-scalar` makes the target operator the identity. Scalar normalization by itself would not have supplied the commuting square.

Step 5 uses the actual untwisted-map definition and the statement of `lem-fix-weil-operations`: tensor evaluation and projection transformations are equivariant on the bounded constructible domains here. Thus cancellation of the Tate line preserves the Frobenius equality. I checked `lem-pur-twist-frobenius-scalar` explicitly states q^d on Lambda(-d) for d>=0 at E and Qlbar; it also states finite-reduction and scalar-extension compatibility. Injectivity and linearity then yield F x = q^d x. Those last two implications are elementary; no general theorem was disguised in a new node.

Step 6 uses `lem-pod-proper-coincidence-frobenius` rather than the weaker finite-stage corollary. I checked that it is stated for all four coefficient stages, that its kappa is a natural isomorphism, and that it requires the same identity compactification for the two exchanges. The step makes that choice and writes the two equalities: its clause-2 transport identity and naturality with the Weil isomorphism. Their composite is F h = h F_c. The trace reading identifies the proper trace with the compact-support trace composed with h^{-1}; bijectivity and the q^d action follow from the preceding steps. Properness is introduced only here.

I tested d=0, X_0=Spec k_0: H^0 = Lambda and q^0 = 1, both trace maps are the identity and the proper comparison does nothing. For affine space the compact-support assertions use no improper identification with ordinary top cohomology. For a smooth proper connected positive-dimensional X the proper clause applies with the same trace. Empty schemes and disconnected unions do not satisfy the geometric-connectedness setting used for the one-dimensional H^0 clause; for a disconnected union H^0 would instead have one copy per component, which shows why that hypothesis is essential. Both field stages have ell!=p and d>=0. No argument here asserts the corresponding general degreewise statement over a nonfield coefficient ring.

For B, no new nodes or unsupported leaf claims exist, and all seven logged searches are preserved exactly. The first Loogle query had an unknown identifier and is recorded as unavailable; the second accepted query had zero hits. The two semantic searches returned group/continuous cohomology, and LeanSearch returned algebra traces and homological support results, none an etale trace theorem. For C, each cited statement was opened and twenty verbatim quotes are stored; all proof dependencies are exactly the union of `uses`, and a traversal from them found no return path to the item. For D, the existing duality corollary is reused and the extra argument is in the item's own steps. For E, I checked the field/finite domains, canonical maps and properness as described above. All six steps are under 1,300 characters; none hides a long standard comparison. There is no SGA citation or route change.

The unit's proper trace assertion is the proper specialization of this item's statement, but its additional point-class normalization at finite and integral coefficients is a separate assertion. This item does not realize that full unit by itself, so I did not overwrite the unit's `realized` fields. Generic coefficient-descent and equivariance tools from other units are explained in `split_report.tool_uses`; the constant-coefficient duality route is retained.
