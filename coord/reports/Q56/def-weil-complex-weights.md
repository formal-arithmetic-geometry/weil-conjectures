# Worker report: def-weil-complex-weights

## Files written

- `dag/nodes/sec-deligne-laumon-a1/def-weil-complex-weights.json`: definition, split using existing nodes; no Mathlib match.
- `citations.json`: empty list, because this definition has no proof steps.
- `report.md`: this report. No new nodes and no Mathlib leaves.

## Attachments

None for the whole item. The project declaration `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost` in `lean/WeilConjectures/DeligneLaumon/Reduction/Weights.lean:352` and `AlgebraicGeometry.WeilComplex.isMixedOfWeightsAtMost_iff` in `lean/WeilConjectures/WeilSheaf/ComplexWeights.lean:57` cover only the upper-bound clause. The latter module explicitly states that the lower half is not formalized. Its single-complex and degree-zero equivalences likewise do not supply Verdier duality, lower weights or purity. These are partial coverage, not an ATTACH claim.

## Wanted literature

None.

## Corrections and source comparison

I read the complete current blueprint definition in `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/def-weil-complex-weights.md`, compared the live imported text, and read BBD, *Faisceaux pervers*, §5.1.8, printed pp. 126–127. The upper bound uses the cohomological shift w+j; the lower bound is the upper bound -w of the Verdier dual, and purity is their conjunction. All three predicates and every hypothesis are retained. BBD supplies the weight convention, while the blueprint specifies the chosen iota and strict Weil-pair framework; no derived category of Weil sheaves or triangulated structure on pairs is assumed.

The import had all three formulae but did not name the theorem constructing its canonical dualizing Weil lift, nor the constructible cohomology functor and its Frobenius commutation. I added the already existing `cor-coef-verdier-weil-equivariance`, `prop-constructible-truncations`, and `def-weil-constructible-heart` as statement dependencies. I wrote out the induced cohomology Weil datum and specified the inverse in the contravariant Hom variable. The notation H^j(K) now includes this datum, making its input to the mixed-Weil-sheaf predicate explicit. These are typing and dependency clarifications, not a change of the definition. No STATEMENT-DISPUTED is needed.

I replaced the generic scheme-property collection dependency by the actual definitions of separatedness and finite type, and linked the Weil-pair and derived-Hom notions where used. The optional ambient-admissibility definition remains a negative comparison only; it is not a hypothesis. The imported blueprint metadata and flags are retained, `same_as` is now [], and no unit realization is changed: this item is a supporting definition, not the unit key theorem.

## Unfinished work

None at this one-level stage. Existing dependencies retain responsibility for constructing and proving the properties of their own operations. No Lean file was written and no compiler was run.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for weights, complex weights, dualizing objects and cohomology sheaves found existing duality and truncation nodes, which were reused. `sk-d-dl-general-weights` supplies the upper-bound convention only; it does not state the whole dual-lower-bound definition and is not recorded as `same_as`. The finite-stage `def-trf-dualizing-complex` is not substituted for a Qbar-coefficient Weil construction. The site-perfect-first-argument node `lem-pod-geometric-frobenius-internal-hom-comparison` is not applied to an arbitrary constructible complex.

## Review by Q56

I checked the definition as a construction, rather than assigning artificial proof steps to its defining formulae. Consequently proof and proof_deps remain empty and citations.json has no step citations. There are no long proof steps or new nodes to audit. I read delivery-errors B–E in full and checked the following substantive points against the actual dependency statements.

For the finite-field and Frobenius paragraph, `def-weil-finite-field-fiber` fixes precisely q=p^a, k0, k, coefficient fields and the geometric fiber. `def-weil-frobenius-detailed` specifies gamma as inverse q-power Frobenius and g_Y over Spec(gamma); I did not treat it as a k-linear morphism. The separatedness and finite-type nodes define the scheme hypotheses directly. For the exceptional object, I read `def-weil-exceptional-inverse-image` at all coefficient stages and `def-weil-exceptional-adjoint-admissibility`: the former constructs the constructible functor without the latter's ambient assumption. Thus a_Y falls under the former, even for a proper scheme whose ambient adjoint condition fails.

For the dual, I read the full statement of `cor-coef-verdier-weil-equivariance`. It treats separated finite-type k0 schemes, E and Qbar coefficients, and exactly the same pairs (K, theta) as `def-weil-weil-sheaf-complex`; it says that duality sends Weil complexes contravariantly to Weil complexes and that the exceptional adjunction lifts with equivariant units and counits. Those are precisely the construction facts used, including the canonical lift of a_Y^! of the coefficient unit. This avoids an arbitrary Weil lift, which would alter the lower weights. The internal Hom is the common-stage operation of `def-weil-derived-pullback-tensor-hom`, not a sheaf Hom out of a lisse argument. No site-perfectness or smoothness is added. The corollary supplies the constructible typing for this particular internal Hom, so I do not assert closure for every pair of constructible arguments merely from an operation's definition.

For the cohomology paragraph I read `prop-constructible-truncations` in full: its statement gives common-finite-stage cohomology, a bounded standard t-structure, scalar compatibility, and commutation with pullback by every scheme automorphism. Taking h=g_Y yields exactly the first arrow in the displayed Weil datum. Applying the cohomology functor to theta_K gives the second arrow and its inverse by functoriality. `def-weil-constructible-heart` defines the heart in which the result lies. The general ringed-site `def-weil-derived-cohomology-sheaves` alone would not justify cohomology at localized/common-stage coefficients, so I explicitly cite the truncation proposition as well. Finally `def-weil-punctual-weights` defines mixed weights by a finite filtration of constructible Weil subsheaves with punctually pure quotients, exactly the predicate used degree by degree.

I checked small cases: the zero complex and the empty scheme satisfy both bounds vacuously (zero sheaves have the length-zero filtration). On Spec(k), a one-dimensional Frobenius eigenvalue alpha of iota-weight v has dual eigenvalue alpha^{-1}, so the two definitions give v<=w and v>=w, respectively. A degree-a complex containing a sheaf of weight v gives v<=w+a; in particular a shift K[n] changes the weight bound by +n, in agreement with BBD and the existing Lean upper-bound lemma. These checks rule out a reversed shift or a missing inverse in the dual datum. Choosing an arbitrary scalar Weil lift for the dualizing object would fail the point test, hence I kept the canonical lift requirement.

I read the hits of all seven logged Mathlib queries, including the second phrasing, and inspected Mathlib's canonical derived t-structure and Finsupp weight definitions: the former bounds degrees of nonzero cohomology, while the latter sums exponent weights. Neither defines Frobenius weights. The first Loogle query had an unknown identifier and supplied no evidence of absence; the second name query and the semantic searches cover that failed phrasing. The AlgebraicGeometry grep has no hits. Search records reproduce only commands actually run.

The two added construction theorems are declared as generic tool uses in split_report: no part of the affine-line estimate's proof is replaced. All other references are statement notions. No SGA source was used.
