# Stage-1 report: lem-trf-permissible-coordinate-chart

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-permissible-coordinate-chart.json`: repaired item split with five corrected proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-blowup-chart-regular-sequence-presentation.json`: new unsplit statement node, Stacks 0BIQ, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-ring-regular-base.json`: new Mathlib leaf, `MvPolynomial.isRegularRing_of_isRegularRing`.
- `dag/nodes/sec-trace-formula/lem-trf-chart-coordinate-nonzerodivisors.json`: new unsplit strict-transform auxiliary statement, no Mathlib match.
- `citations.json`: 21 verbatim statement quotes, one for every cited node in every proof step.
- `report.md`: this report.

## Attachments

None. I searched the project source and the upstream master source for the item id, title, and coordinate-chart terms. No sorry-free project declaration states this item exactly.

## WANTED

None. ILO Exposé VIII and the Stacks sources are present locally.

## Not duplicates

- `lem-trf-blowup-chart-regular-sequence-presentation` vs `lemma-nagata-chart-generator-regular`: the new node identifies the whole chart algebra with a quotient for a regular sequence; the existing node only proves injectivity of multiplication by the chosen generator.
- `lem-trf-chart-coordinate-nonzerodivisors` vs `lemma-nagata-chart-generator-regular`: the new node concerns injectivity after quotienting by each strict-transform coordinate; the existing node concerns the unquotiented affine chart.
- `lem-trf-polynomial-ring-regular-base` vs `lem-weil-pbc-polynomial-ring-field-regular-ring`: the new Mathlib leaf allows any regular base ring, while the existing node is only the field case and is not used for the quotient chart.

## What was wrong and what changed

The returned version's Step 1 used the quotient presentation without a statement of Stacks 0BIQ and did not cite the regular-sequence hypothesis. It also tried to count the maximal ideal by listing only `t_j`, vanishing `u_i`, and outside parameters. That count is false when a `u_i` is a unit; for example, in `k[x,y]_(x,y)` on the `(x,y)` blowup chart at `(x,y,u-1)`, the listed set misses `u-1`. Step 1 now uses the 0BIQ chart-presentation node, the existing regular-parameter quotient node, polynomial regularity over a regular base, the chart-generator nonzerodivisor lemma, and Tag 00NU after localizing.

Step 3 now separates the case `t_j` invertible from the case `t_j` in the prime. In the latter case it computes the linear classes in the cotangent space from `t_i=t_j u_i`: vanishing `u_i` contribute independent classes, unit `u_i` make `t_i` associates of `t_j`, and outside parameters contribute their own classes. These classes are extended to a minimal generating set and the existing regular-sequence node gives the dimension drop. No false maximal-ideal generator assertion remains.

Step 4 now uses the chart principalization statement to identify the off-center part with `D(t_j)`. The `i=j` case is handled because `t_j=0` forces all center coordinates to vanish on this chart, so there is no off-center part. For `i\ne j`, the new coordinate-nonzerodivisor node supplies the density needed to identify the closure of `D(t_j)\cap V(u_i)` or `D(t_j)\cap V(t_i)` with the indicated coordinate hyperplane. The two regular-local nodes and the two closed Nagata chart lemmas are declared explicitly as tool uses in the split report, including the two `sk-thm-p1` tools required by C8.

## Review by NZ

I reread ILO Exposé VIII, Lemma 4.2.9 at printed page 121, its setup in §§4.1.2–4.1.4, Stacks 0BIQ in `more-algebra.tex`, and Stacks 00NU in `algebra.tex`. The item statement remains the same as the ILO coordinate calculation, including arbitrary nonempty `J`, `J` meeting the boundary indices, the empty product `I=∅`, and the `i=j` empty strict-transform case. The 0BIQ node states exactly the presentation used in Step 1, with the regular-sequence hypothesis. The existing `lem-exc-regular-local-lift-regular-sequence-quotient` node states the 00NU local lifting criterion used after localization. The polynomial leaf is the finite-variable specialization of Mathlib's `MvPolynomial.isRegularRing_of_isRegularRing` at `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean:108-114`. The coordinate-nonzerodivisor node is the strict-transform density subclaim, distinct from both the chart presentation and the unquotiented chart-generator lemma.

Step 1 cites the regular-parameter node for permutation, regular sequence, and the regular quotient `R/(t_i:i∈J)`; it cites 0BIQ for the displayed chart presentation; it cites the Mathlib polynomial leaf and the regular-local localization node for regularity of the quotient; it cites `lemma-nagata-chart-generator-regular` for injectivity of multiplication by `t_j`; and it cites 00NU for the local chart regularity conclusion. I checked both prime cases: if `t_j` is absent, the chart is the corresponding localization of `R`; if `t_j` is present, the quotient by `t_j` is the polynomial ring over the regular parameter quotient and the nonzerodivisor hypothesis persists under localization.

Step 2 cites the principalization node for the center ideal `(t_j)`, then uses the displayed substitutions and the reduction and closed-immersion definitions. I checked repeated factors of `t_j`, coordinates with indices in and out of `J`, and the support after reduction.

Step 3 cites the regular-sequence and localization nodes. I checked the old counterexample `(x,y,u-1)` explicitly: the revised argument uses the class of `u-1` in the completed cotangent calculation rather than claiming the set `{x}` generates. For `t_j` invertible, the `u_i` equations are associates of the corresponding `t_i`; for `t_j` in the prime, the relation `t_i=t_j u_i` gives the stated first-order independence. Extending the independent classes to a minimal generating set and applying the regular-sequence node gives one dimension drop per selected equation, including the cases of no selected equations and an empty intersection.

Step 4 cites the strict-transform definition, chart principalization, the new coordinate-nonzerodivisor node, reduction, and closed immersions. I checked `i=j` on the `(x,y)` blowup chart, where `x=0` forces `y=0` and the chart has no part over the complement of the center; for `i∈J\{j}`, `t_i=0` becomes `u_i=0` on `D(t_j)`; for `i∉J`, `t_i` is unchanged. The nonzerodivisor clauses ensure these hypersurface closures are scheme-theoretically the stated coordinate quotients.

Step 5 uses only the global blowup definition, reduction, strict-transform definition, and the codimension convention to glue the standard charts and record the empty-product case. The proof steps are under 2000 characters each, so no hidden long lemma remains. I reran the required Mathlib searches for each new node using LeanFinder, Loogle, grep, and LeanSearch; the exact queries and outcomes are recorded in the node records and the sandbox search log. No statement was corrected, no SGA source was used, and no cycle was introduced.
