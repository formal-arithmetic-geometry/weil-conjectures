# Stage-1 report: lem-sfb-cauchy-green-test-function

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-cauchy-green-test-function.json`: item split into six steps; exact statement and full inherited blueprint ancestry retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-planar-polar-integration.json`: Mathlib leaf, the nonnegative and complex polar formulas with an arbitrary center.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integrable-majorant-estimate.json`: Mathlib leaf, integrability by domination and the norm bound for an integral.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cauchy-green-annulus-formula.json`: new statement-only C1 annular Green theorem, searched but not a Mathlib leaf.
- `citations.json`: one verbatim statement excerpt for each cited node in each proof step.

## Attachments

None. Searching `lean/WeilConjectures` by the item tag and Cauchy–Green/test-function concepts found no project declaration proving this statement. The existing Mathlib Cauchy-circle formula has a complex differentiability hypothesis; it does not apply to a general real-smooth test function.

## WANTED

WANTED: J.-P. Demailly, *Complex Analytic and Differential Geometry*, I §3.A, formula (3.2) and proof, printed p.21, for the item and `lem-sfb-cauchy-green-annulus-formula`. The PDF is absent from the local literature. Online fetches of the supplied manuscript URL and its former university-domain URL timed out. I did not obtain or read the book during this split. Accordingly the item's proof is explicitly marked `proof_origin.by = agent`. Its original bibliographic pointer is retained as the intended reference, not presented as a verified reading.

The sources I actually read are `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean:185–218`, `Mathlib/MeasureTheory/Group/Integral.lean:86–95`, `Mathlib/MeasureTheory/Group/LIntegral.lean:47–57`, `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:83–103`, and `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:934–952`. For the annular node I also read `Mathlib/Analysis/Complex/CauchyIntegral.lean:186–261` and its annulus discussion: it supplies only a rectangle formula for real derivatives and annulus formulas under holomorphicity, so there is a genuine missing lemma.

## Not duplicates

lem-sfb-planar-polar-integration vs lem-sfb-cauchy-circle-formula: product area integration with a radial Jacobian is different from evaluation of a holomorphic function by a line integral.

lem-sfb-integrable-majorant-estimate vs lem-sfb-continuous-compact-support-integrable: the new leaf treats arbitrary measures and measurable functions with an integrable majorant and supplies a norm estimate; the existing leaf supplies integrability under continuity and compact support.

lem-sfb-integrable-majorant-estimate vs lem-sfb-locally-integrable-parametric-convolution: the new leaf is generic integral domination; the existing leaf concerns smoothness and differentiability of convolution.

lem-sfb-cauchy-green-annulus-formula vs lem-sfb-cauchy-circle-formula: the existing node requires complex differentiability on a disk and recovers a value at its interior point; the new node treats arbitrary real C1 functions on a nonsingular annulus and computes their bar-derivative area integral from two boundaries.

lem-sfb-cauchy-green-annulus-formula vs lem-sfb-scalar-integrable-integration-by-parts: the existing node has a whole-space directional integration-by-parts statement with no boundary term; the new node retains the two oriented circle boundary terms.

Searches of the whole DAG for the new declarations and concepts found no exact or more general statement node. The incidental radial-extension and Weil-weight bounds returned by broad word searches were opened and have unrelated statements. Whole-blueprint searches for Cauchy, Cauchy Green, polar, polar integration, annulus, norm_integral, majorant, and integrable domination returned no match. The ancestor tool prints `blueprint.from.node = None`; I preserved the item's long recorded place and entire via chain, and each new node adds the item in front of that chain.

## What was wrong and what changed

The imported statement is mathematically correct and has not been changed. It had no proof. An initial draft moved inverse-norm local integrability to its own node, duplicating an item clause; I removed that uncommitted node. The final item instead performs the polar calculation itself from a general Mathlib leaf. I replaced a qualitative appeal to convergence of annular integrals with the explicit omitted-disk bound `2 pi M epsilon`, and replaced an implicit passage under a circle integral with the explicit continuity modulus bound `pi omega(epsilon)`. Neither limit hides an uncited convergence theorem.

An initial search command mistakenly used a proposed new node ID as the command's second argument rather than the delivery item ID. The delivery search gate correctly rejected the missing entries in this item's log. I reran the retained annulus searches under the correct item and used new correctly logged searches for the two Mathlib leaves. The node records now use exact tool/query strings and include the actual returned log records as their results; queries with invalid identifiers are recorded as such, not evidence of absence. Inherited searches on the item are preserved.

## Review by Q28

I read the worker brief, stages/1-dag.md, the three-level contract in SETUP.md, GOAL.md, the chapter and unit records, and delivery-errors B–E. This is a supporting analytic input below the fixed unit route; the delivery changes no target, coefficient category, chapter, or unit statement. It uses no SGA source. I performed the attachment search in the live Lean source and checked the available upstream source for the Cauchy–Green concepts; nothing supplied a closed attachment.

For step 1 I checked the *nonnegative*, not merely Bochner, polar identity: a finite Bochner value alone would not prove integrability. After multiplication by the Jacobian, the reciprocal-norm integrand is exactly the indicator of a finite rectangle, giving `2 pi s`. The same statement proves zero area for a singleton and a circle. The majorant node then proves integrability of the actual measurable restriction of k to every compact set. I verified the source lines 214–218 for the nonnegative formula and 207–212 for the complex clause, and the two generated additive translation declarations at Group/LIntegral.lean:53 and Group/Integral.lean:92. Substitution `w ↦ f(c+w)` followed by the translation rewrite is the promised one-line centered specialization.

For step 2, the cited majorant statement has exactly the integrability hypothesis needed for `M q_{z,R}` and the measurable-function hypothesis needed for `F`. The support of a derivative is contained in the support of u because u is identically zero locally off that support; hence continuity supplies the finite bound M. The polar node is cited for the centered radial majorant and its integral from step 1, with no hypothesis that z lies in the support.

For step 3, the cited annulus statement supplies the area-to-boundary identity with *both* circles counterclockwise and an explicit subtraction of the inner one. Its domain hypothesis holds on the open set C minus {z}. The proof writes the reciprocal's two real derivatives, so the vanishing bar derivative is a calculation and does not silently impose holomorphicity on u. The outer circle is outside the compact support. I checked the annulus statement independently: for `V(r,t)=v(c+r exp(it))`, the identity `d_r(i r exp(it) V)-d_t(exp(it) V)=2 i r (bar-partial v)(c+r exp(it))`, integrated on the polar rectangle, gives precisely its formula; the angular endpoint terms cancel by periodicity. This is a proof route for the future worker, not proof text hidden in the new node's statement. Demailly remains WANTED rather than falsely claimed as a read source.

For step 4, division by the denominator along the inner circle contributes a *minus* sign to the contour integral, which cancels the minus inner-boundary sign: the result is `A_epsilon=(1/2) integral u`. The majorant node applies to the restricted interval measure and its constant integrable bound, giving `|A_epsilon-pi u(z)| <= pi omega(epsilon)`. I checked the direct epsilon–delta argument for `omega(epsilon) -> 0`; no differentiation under an integral is asserted.

For step 5, the polar calculation and majorant statement give `|I-A_epsilon| <= 2 pi M epsilon`. The singularity is integrable, and boundary circles are null as already proved. Step 6 is just the triangle inequality and a nonnegative quantity bounded by something tending to zero. I verified all citations against the actual statement strings and generated citations.json by extracting those strings. No non-elementary step exceeds 2000 characters. The new annulus node is a reusable nonsingular boundary theorem; neither Mathlib leaf restates an item clause.

I tested the formulas on empty support (M=0), z outside the support, and u constant near z (the inner boundary is exactly pi u(z) for small epsilon). For the annular theorem, v=1 gives zero on each side; v=bar(zeta-c) gives area pi(R^2-r^2) on each side and checks the factor and orientation. For the polar leaf, the nonnegative function may have infinite integral, and the formula still applies; the complex clause requires integrability. For the majorant leaf, zero majorant forces F=0 almost everywhere and the empty measure space poses no problem.

## What remains

The nonsingular C1 annulus lemma is intentionally statement-only for a later stage-1 worker. The item is fully assembled from its stated inputs. Source comparison with the absent Demailly book remains pending; this limitation is recorded above and in proof_origin. No Lean files were written and no compiler, Lake, or build was run.
