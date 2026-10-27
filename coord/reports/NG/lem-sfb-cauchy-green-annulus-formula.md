# Stage-1 report: lem-sfb-cauchy-green-annulus-formula

Group NG, 2026-10-24. Direct delivery; no second worker or other agent was started. All writes are confined to this item's sandbox. No Lean was written, opened through an LSP, compiled or built.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-cauchy-green-annulus-formula.json`: item, split into six steps; statement unchanged. The previous source, blueprint ancestry and five Mathlib search records are retained. Three fresh searches of the item are appended.
- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-partials-frechet-criterion.json`: new statement-only, unsplit. Continuous coordinate partials give the real Fréchet derivative and its continuity. No Mathlib match found after two semantic phrasings and source inspection.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rectangle-divergence-integral.json`: new statement-only Mathlib leaf, `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`, `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:482–494`.
- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-on-compact-integrable.json`: new statement-only Mathlib leaf, `ContinuousOn.integrableOn_compact`, `Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:592–594`.
- `citations.json`: one verbatim statement quote for each step/node citation (six entries).
- `searches.jsonl`: actual msearch.py records, with hits read before the verdicts were written.
- `prepare.py`: reproducible sandbox-only JSON preparation script.
- `report.md`: this report.

There are three new nodes, two Mathlib leaves. New nodes have empty proofs and proof dependency lists. The two Mathlib leaves have their declaration, file, line and one-line specialization recorded. The remaining new node is genuinely a general calculus prerequisite, not a restatement of the annulus identity or one of its clauses.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact item id, Cauchy–Green, annulus, and continuous partial derivatives found no declaration proving the item or the new nodes. No Mathlib declaration is claimed as a project attachment. The existing project-source hits concerning finite partial products are group-theoretic and irrelevant.

## Wanted sources

WANTED: Demailly, *Complex Analytic and Differential Geometry*, I §3.A, formula (3.2) proof, printed p.21, for lem-sfb-cauchy-green-annulus-formula. The file named by the imported item is absent. The imported node honestly already recorded that failure; I did not fetch or claim to read the book. The completed annulus proof is agent-written from the locally read rectangle divergence theorem and the existing polar integration statement.

WANTED: Rudin, *Principles of Mathematical Analysis*, third edition, Theorem 9.21, for lem-sfb-continuous-partials-frechet-criterion. This standard reference is not locally available and has not been read; its source field explicitly says WANTED and agent formulation. A future split can telescope the increment along coordinate segments in a small box in U, use the one-dimensional mean-value estimate for the remainder on each segment, and use continuity of the partials to obtain the little-o estimate. This is only a proposed argument in the report, not a proof hidden in the new statement.

## Errors or discrepancies

No statement dispute: the imported annulus statement is correct, including its factor 1/(2i), its two counterclockwise parametrizations, and absolute convergence. Its proof was empty. The polar change of variables already exists as lem-sfb-planar-polar-integration and was reused.

The inherited ancestry has `blueprint.from.node = null`; `tools/blueprint_refs.py ancestor lem-sfb-cauchy-green-annulus-formula` prints None. I retained that ancestry and its complete via chain and exact inherited place. The latest blueprint is main-20261024 (ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its current direct-images proof (3) and its unit; this is an analytic tool far below that route, not a replacement for its direct-image step. Searches of the whole imported blueprint for Green, divergence, rectangle, polar, continuous partial and coordinate differentiability found no matching analytic blueprint node. The rectangle hits concern category-theoretic commutative squares, not analytic rectangles.

Two tempting identifications were rejected. The complex annulus lemmas in CauchyIntegral.lean:315–363 assume complex differentiability and cannot prove this real C1 statement. Also, `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` (MeanValue.lean:807) presupposes full Fréchet derivatives, whereas the item initially assumes only coordinate partials. Treating either as an exact match would hide part of the proof.

## Unfinished obligations

The requested one-level split is complete. The new coordinate-partials criterion remains unsplit as required for a new non-Mathlib node; it is not being claimed proved. All other non-elementary inputs in the item's proof are existing nodes or the two new Mathlib leaves. No source was downloaded, no forbidden source was cited, and no unit/chapter record was changed.

## Not duplicates

lem-sfb-continuous-partials-frechet-criterion vs lem-sfb-real-smooth-differentiation: the existing node gives rules for already existing differentials and smooth functions; the new node constructs the full real differential from continuous coordinate partials of a merely C1 function.

lem-sfb-continuous-partials-frechet-criterion vs lem-sfb-complex-analytic-derivative-rules: the latter concerns complex derivatives and complex analytic functions; the new criterion concerns real differentiability of functions not assumed holomorphic.

lem-sfb-continuous-on-compact-integrable vs lem-sfb-continuous-local-integrability: the latter gives neighbourhoodwise integrability on an open set; the new leaf gives integrability on an arbitrary compact set, including intervals and closed annuli, without asking for an open domain.

lem-sfb-continuous-on-compact-integrable vs lem-sfb-continuous-compact-support-integrable: the latter assumes a globally continuous function with compact support; here a function is given only on a compact subset and its zero extension need not be continuous across the boundary.

lem-sfb-rectangle-divergence-integral vs lem-sfb-cauchy-green-annulus-formula: the new leaf is the independent two-component real rectangle divergence theorem, with arbitrary vector field components and derivative fields; the parent proves the polar pullback identity, cancels the seam, changes area coordinates, and identifies the two circle integrals. The new leaf neither states an annulus formula nor assumes a complex derivative.

No Stacks tags are applicable to these real-analysis inputs, so there are no same-Stacks-tag pairs. I searched the whole DAG by the relevant concepts and by the exact Mathlib declarations before creating these nodes. The only occurrences of `ContinuousOn.integrableOn_compact` in older nodes were search-result mentions, not statements of that theorem. Existing polar integration is cited rather than duplicated.

## Review by NG

I read delivery-errors B through E and checked the item and the three new statements against those failure modes. I read the complete statements of every cited node, not merely its title or proof: the new criterion, compact integrability, rectangle divergence, existing real-smooth-differentiation and existing planar-polar-integration. The quotes in citations.json are copied from those statements; the real differentiation citation quotes only its pointwise rules. In particular I did not use the smoothness conclusion of that node on a C1 function.

For step 1, the criterion applies to m=2 and the given open V because both coordinate partials exist everywhere and are continuous. Its statement supplies both the differential formula and continuity of v. No extra assumption of holomorphy is introduced. The continuity of the bar derivative is just the displayed linear combination of the two continuous partials.

For step 2, the cited compact-set theorem actually states integrability on the set, unlike the two existing integrability nodes. A is closed and bounded in the plane; the line-integral parameter domains are compact real intervals. The line integrands are continuous and the speed has norm s. Thus both area and contour absolute-convergence clauses are covered, using only the item's hypotheses.

For step 3, I checked the chain and product rules against the cited node's explicit conditional formulas, which require derivatives already supplied by step 1. The circle-coordinate differentiation and the displayed trigonometric identities are elementary calculations. I recalculated B_rho - P_t: the two i exp(it) w terms cancel, leaving rho(i v_x-v_y), exactly 2i rho bar-partial v. This is a computation, not an unstated polar Stokes lemma. No smoothness beyond one derivative is used. It is marked elementary relative to those cited rules.

For step 4, I read DivergenceTheorem.lean:482–494, including the full hypotheses and its product-volume conclusion. The ordered corners are (r,-pi) and (R,pi); F=B and G=-P give the required divergence. The derivative fields are derivatives on an open neighbourhood of the rectangle, so in particular at every interior point. The divergence is continuous and the compact-integrability leaf supplies exactly the integrability hypothesis. The minus sign on G makes the angle edges cancel because P(rho,pi)=P(rho,-pi). The surviving radial edges are B(R,t) minus B(r,t), establishing the inner boundary sign rather than assuming it.

For step 5, I read the existing polar-integration statement and its source declarations at PolarCoord.lean:207–218. It is centered at arbitrary c, has angular interval (-pi,pi), and applies to integrable complex functions, exactly what is used. The zero extension of the integrable restriction to A is integrable. Since rho>0, the inverse image of A is exactly r<=rho<=R. I explicitly accounted for the angular edges of the closed rectangle, which have product measure zero; I did not conflate its closed interval with the polar lemma's open one. Scalar multiplication of the integrable function accounts for the factor 2i.

For step 6, I checked the change from [-pi,pi] to [0,2pi] by writing the split at zero and the substitution by 2pi on the negative half; periodicity gives equality. The final line integral uses the statement's actual parametrization and derivative i s exp(it). Multiplying by (2i) inverse gives the asserted normalization. These operations only combine already established integral identities.

For the new criterion, I checked m=1, constant functions and the two coordinate projections. For m=2 the claimed differential on x+iy and on x-iy is h_x+i h_y and h_x-i h_y respectively, so real and complex differentiability have not been conflated. The open-domain hypothesis allows the coordinate segments locally. No mere existence of noncontinuous partials is asserted to suffice. For compact integrability, I tested K empty, a singleton, a closed interval and the annulus; the ambient dimensions are >=1, and complex/product-plane volume is the usual real two-dimensional measure. For rectangle divergence, I checked constant F,G, F(x,y)=x with G=0, and zero side lengths. The source theorem permits weak inequalities, so these cases agree, including null rectangles.

As a sign and normalization check on the parent, v=constant and v(z)=z give zero on both sides. For v(z)=conjugate(z-c), bar-partial v=1, the area integral is pi(R^2-r^2), and each counterclockwise contour integral is 2pi i s^2; their difference divided by 2i is the same number. The limit R approaching r also has the right zero difference, though strict r<R remains the statement's hypothesis. No singular kernel appears, so no puncture limit is hidden here.

All six steps are below 2000 characters; none hides a separate comparison lemma. The only substantial prerequisite initially implicit in the C1 assumption was made into the general coordinate-partials criterion. The source of the item is unavailable and this is honestly marked agent-written; the Mathlib leaves are based on signatures actually read. The new nodes have statements only, complete introduced objects and hypotheses, and searches matching the recorded tool calls. There is no circular citation, no use of a cited proof instead of its statement, and no new clause-node that simply restates what the parent must prove.
