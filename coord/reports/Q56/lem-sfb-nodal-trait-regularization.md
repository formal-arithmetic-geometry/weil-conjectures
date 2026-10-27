## Worker report

Stage 1 repair by Q56, 2026-10-22. Four new statement-only nodes; zero Mathlib leaves. The item statement is unchanged. The current human re-split instruction in `coord/repair-notes/lem-sfb-nodal-trait-regularization.json` explicitly reopens this previously reviewed split: retain every argument of its 11,162-character proof, create at least three independently workable nodes, and reduce the item's assembly proof to at most 3,000 characters. The new assembly is 2,479 characters in four steps. This is a substantive stage-1 re-split, not the returned stage-2 rebind.

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-trait-regularization.json`: existing statement, short assembly proof, updated proof dependencies and split report; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-trait-finite-singular-charts.json`: finite singular set, chosen pointed exponent, regularity and dimension bounds; statement-only, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-point-blowup-local-descent.json`: isolation of reduced centres, Cartesian comparison, nodal descent and remaining exponent; statement-only, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-point-blowup-projective-fibres.json`: H-projectivity, finiteness and geometric exceptional fibres of a given point blowup; statement-only, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-trait-curve-surface-components.json`: proper-flat regular scheme with explicit local dimension hypotheses, component dimensions and vertical DVRs; statement-only, unsplit, no Mathlib match.
- `report.md` and `citations.json`: source/hypothesis review and exact verbatim statement quotes for all seven step/node citation pairs.

Attachments: none. The upstream `lean/WeilConjectures` search by blueprint tag, theorem name and nodal-regularization words gave no attachment. The theorem `AlgebraicGeometry.exists_nodal_trait_regularization` exists in `lean/Sheaf/AlgebraicGeometry/NodalTraitRegularization.lean:215`, but its body is `sorry` at line 286. It is a landed statement, not an attachment of a finished proof. The four new statements have no matching project declaration found by the nodal/blowup/regularization source searches; the old parent theorem states the full tower and is not a proof of its new local inputs.

WANTED: none. All sources are present in the read-only literature directory. No statement dispute was found. The existing correction of Stacks' stopping threshold is retained: for n=3 the middle chart is rs=pi and is regular, although the last paragraph of 0CDE says there is a singular point for every n>2. This is a source-proof correction, not a change to the item's statement.

## Repair of the return

A7 (superseded rebind): the initial dry run of the retained packet exited with the missing-review-heading error. Comparison of the retained node against live found only the inappropriate lean rebind and the later maintainer audit field. The reviewed NU stage-1 proof and NS stage-2 ownership are now the starting point. The live human re-split instruction authorizes the actual new stage-1 work described above; it is not an unchanged re-push.

A2: this report now includes the required substantive `## Review by Q56` below. The historical report and its headings remain at the end for continuity; its proposal to set existing:true is explicitly superseded.

H1/H2: the entire live `lean` object is preserved, including `existing:false`, `by:NS`, `branch:sheaf-dag`, its full statement and `file:lean/Sheaf/AlgebraicGeometry/NodalTraitRegularization.lean`. The live `reviewed`, `reviewed_lean`, `lean_audit`, `created`, `tool_uses`, statement, statement dependencies and blueprint metadata are retained. No Lean file is created or edited; no compiler, Lake or build command is run. Only stage-1-owned proof fields and the four new DAG nodes change. The module continues to have its original owning node.

## Responsibility map and arguments retained

The old proof is reproduced in full in the appendix, with each argument assigned below. The new nodes contain statements only, empty proof/proof_deps and null proof_origin, so other workers can take these arguments independently.

1. Original steps 1--3 belong to `lem-sfb-nodal-trait-finite-singular-charts`. This task proves Noetherianity, uses the first-Fitting closed unramified singular subscheme and its empty generic fibre to get a finite discrete special set, obtains the 0CDD pointed model, excludes ab=0 using the generization in its nodal section and etale-local smoothness, and applies arithmetic-chart regularity/dimension. The finite set is not merely assumed; all of that first original argument remains required by the new statement. Choice of exponent is local; no invariant under different choices is asserted or needed.
2. Original steps 4--6 belong to `lem-sfb-nodal-point-blowup-local-descent`. This task isolates u in both finite etale fibres over the reduced centres, identifies the scheme-theoretic inverse images, applies flat blowup base change, proves the etale map above x covers the whole fibre, checks the outer and middle charts and descends flatness/lfp/nodality. It also descends the unique rational residual singular point through the common pointed diagram for n>=4; for n=2,3 there is none. The statement explicitly requires all these comparisons, not just the conclusion that a blowup exists.
3. Original steps 7--8 belong to `lem-sfb-nodal-point-blowup-projective-fibres`. This task proves finite generation of the reduced-point ideal on Noetherian X, applies H-projectivity over the affine Noetherian base (not only projective-bundle projectivity), derives properness, qc/qs and finite presentation from the lfp hypothesis, and computes geometric exceptional fibres through the Cartesian diagram. It must pass from a residue extension splitting the local model to an algebraic closure of kappa(x), and then to every field extension using geometric-connectedness testing. The two projective lines have a common point; off x the blowup is an isomorphism and its fibres remain points. Surjectivity gives preservation of nonempty family fibres. The new lemma assumes flatness and lfp of the blowup family, which task 2 supplies; it does not quietly prove them from projectivity.
4. Original steps 9--10 remain in item steps 2--3: the explicit inner induction on floor(n/2), then outer induction on the number of original nonregular points; and the invariant that the composite stays an isomorphism over the original smooth locus. Their base cases and decrement are written out. Each finite sub-tower fixes all other original singular points.
5. Original steps 11--12 belong to `lem-sfb-regular-trait-curve-surface-components`. This task decomposes regular Noetherian T into integral clopen components, excludes vertical components using injectivity of multiplication by pi on flat local rings, specializes each proper component from the generic point to a closed special point, and converts its local dimension two and the upper bound into component dimension two. At a special-component generic point it identifies A/pi A with the field local ring of the reduced special fibre, obtains the maximal ideal (pi), and applies the principal-maximal-ideal DVR criterion with pi nonzero. These are explicit hypotheses/conclusions of the new statement. It works without nodality and takes the dimension bounds as hypotheses, which task 1 supplies for the terminal nodal family.

## Validation

The repaired packet passed the required server dry run: `OK (not pushed) deliver/Q56/lem-sfb-nodal-trait-regularization at 99175a54b7b: preflight passed`. Local comparison found that only proof, proof_deps and split_report differ on the existing item; all statement and ownership fields match live exactly. This report correction is checked by the final dry run before pushing.

## Searches and reuse

The whole DAG was searched by the tags 0CDE, 0CDD, 0CDC, 0805, 02NS, 033M, 04MU and 00PD and by nodal/regular/blowup/finite-singular/dimension keywords. Nearby statements were opened, including the existing trait normal forms, arithmetic chart calculus, projective affine-base blowup, regular-point blowup defects, normal components and dimension-supremum results. The four tasks use those interfaces when later split; no replacement normal-form, chart-calculus, projectivity-only or regular-normal node was made. The blueprint was searched with `tools/blueprint_refs.py search` for nodal, blowup, regular surface and singular locus. The first, third and fourth returned zero; the blowup results are generic Nagata constructions or other geometric settings, none one of these four statements. `ancestor` returned null; new blueprint.from.node remains null, with the existing ancestry in via prefixed by the item and a precise responsibility place. No chapter/unit route or unit realization changes.

Each new node records five exact msearch.py queries under this item: two differently phrased LeanFinder searches, Loogle, grep of Mathlib/AlgebraicGeometry, and LeanSearch. All are in searches.jsonl. LeanFinder and Loogle returned successfully. LeanSearch returned `Rate limit exceeded: 60 per 1 minute` for all four queries, recorded as unavailable, never as absence. The successful greps for nodal and blowup returned no hits. The connectedness grep returned the class and fibre/base-change interface in Mathlib/AlgebraicGeometry/Geometrically/Connected.lean:40--74, not an exceptional-fibre computation. The regular/DVR grep returned EllipticCurve/Reduction and OrderOfVanishing:107, the latter already assuming a DVR stalk. The second semantic phrasings returned smooth/etale locus localization, standard-smooth coordinates, properness of Proj, universally-closed-over-a-field global sections and integral scheme predicates. I read Smooth.lean:129--147, RingTheory/Smooth/Locus.lean:43--59, Proper.lean:137--159, Connected.lean:32--74, OrderOfVanishing.lean:95--118 and the Weierstrass minimal/reduction section:206--245. They do not establish any whole new statement or a one-line specialization of it. No Mathlib leaf is claimed.

## Review by Q56

I read the item against Stacks models.tex Tags 0CDC/example-blowup, 0CDD/lemma-etale-local-at-worst-nodal and 0CDE/lemma-blowup-at-worst-nodal, including the omitted generic-node exclusion and the Cartesian blowup argument. I also read divisors.tex Tag 0805/lemma-flat-base-change-blowing-up and Tag 02NS/lemma-blowing-up-projective, properties.tex Tag 033M/lemma-normal-Noetherian and Tag 04MU/lemma-dimension, and algebra.tex Tag 00PD/lemma-characterize-dvr. The new finite-chart task is the first paragraph plus the pointed models and dimension calculation; the local-blowup task is the two Cartesian squares and descent of chart singularities; the projective/fibre task adds the affine-base H-projectivity input and the explicit exceptional charts; the component task is the proper-flat application of normal decomposition, local dimensions and 00PD(4). I checked that no excellence or complete-DVR argument has entered.

For item step 1 I opened the finite-singular-charts statement. It assumes precisely a flat finitely presented smooth-generic nodal family, allows disconnected/empty fibres, and concludes the finite closed nonregular set and model exponents >=2 used here. The item's nonempty-fibre hypothesis is stronger and causes no loss. Its Noetherian conclusion supplies the hypothesis needed for projective/fibre control.

For step 2 I read both new point-blowup statements. Local descent assumes a chosen common pointed etale model of exponent n>=2 and gives exactly the residual exponent n-2 and the two stopping cases, plus flatness/lfp and preservation of nodality. Projective-fibres assumes a Noetherian H-projective scheme, the same pointed diagram and the already established flat/lfp blowup family, and concludes H-projectivity/finite presentation/Noetherianity, nonempty connected geometric fibres and preservation of nonempty family fibres. Thus it applies at the first blowup and at each later one. The induction counts a chosen diagram, not a canonical exponent. Away from the centre the morphism is an isomorphism, so no other original point has changed. The inner base cases n=2 and n=3 and the outer base case E empty are explicit. The statement of neither new node is a finite resolution theorem; the termination argument stays in the item.

For step 3 I opened thm-nagata-global-blowup-complement: its statement gives the restriction over the complement of the ideal's zero set as an isomorphism, which for the reduced-point ideal is the complement of the chosen point. The finite-chart statement gives regularity on the relative smooth locus. Those statements justify the written induction on the current inverse image of the original smooth locus. It is essential here that centres are nonregular total-space points, not all nodes of the special fibre. In particular xy=pi is left alone.

For step 4 I read the component statement and checked each hypothesis separately: the last family is proper by H-projectivity, flat and Noetherian by step 2, regular by termination, and has reduced special fibre by nodality. The finite-chart statement applies again because all intermediate generic fibres stayed isomorphic to X_K and supplies the two local dimension hypotheses. The component statement explicitly concludes the finite clopen integral regular surfaces and DVR stalks at special generic points. Its maximal-ideal claim uses the actual total-space stalk A and A/pi A, not the completed stalk or an unrelated fibre ring. The empty-component case is allowed in that general statement, whereas the item's nonempty fibres imply nonempty terminal T.

Small cases for the new finite-chart task: the empty scheme is vacuous; a smooth proper curve model has no nonregular points; xy=pi has a nonsmooth special point but regular total space; the excluded xy=0 model fails the smooth-generic hypothesis. For local descent: xy=pi^2 gives middle rs=1 and no remaining singularity; xy=pi^3 gives rs=pi and no remaining singularity; xy=pi^4 leaves rs=pi^2 and requires a second blowup. Two independent original nodes are unaffected away from the selected one. These tests also cover the zero and one-step induction cases.

For projective/fibre control I checked the exceptional conic for n=2 and the two-line union for n>2; non-split residue forms become these after algebraic closure, not necessarily over kappa(x). I checked that geometric connectedness is explicitly nonempty after every extension, and not just ordinary connectedness over the original residue field. For the component task, P^1_R and a disjoint union of two P^1_R give respectively one and two dimension-two components; the empty scheme is allowed; a component only over k violates flatness, and a model only over K is not proper over R, explaining why both hypotheses are needed. Nonreduced special fibres are excluded before identifying A/pi A with a field. Imperfect residue fields and characteristic two add no assumption in any new statement.

Against B--E: all four nodes are self-contained statements with definitions cited, sources by actual tags/labels, empty proofs and proof dependencies, exact logged searches, and complete ancestry fields. No new node states the full finite tower. The two nontrivial global tasks have distinct hypotheses: projective-fibres does not prove nodal descent, and regular components assumes regularity/dimension bounds and does not resolve anything. Seven citation quotes are copied verbatim from statements, and proof_deps is precisely their uses union. Each new stmt_dep was opened; the geometric-connectedness definition really quantifies over all field extensions, and regular-scheme includes locally Noetherian regular stalks. Algebraic-closure references were made explicit in the first three new statements. No item step exceeds 2,000 characters. The earlier stage-2 report's assertion that a sorried declaration may be attached was corrected; the source file and ownership were restored without rewriting any Lean record. The full old mathematical argument is kept below rather than shortened away.

## Not duplicates

lem-sfb-nodal-trait-finite-singular-charts vs def-sfb-surface-point-blowup-data: the existing node defines centre ideals, exceptional fibres and transform chains; it proves none of the geometric assertions of this task.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-common-nodal-model: the existing theorem compares two marked possibly smooth-generic-failing models; it gives neither a finite singular-chart analysis of one family nor the local point-blowup comparison required here.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-dvr-nodal-etale-local-form: the existing normal form allows ab=0 and does not give global finiteness, nonregularity criteria, local dimension bounds or any blowup assertion.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-nodal-log-dualizing-pullback: the existing theorem concerns logarithmic dualizing line pullback along a given nodal modification; it proves none of the finite-chart or exceptional-fibre assertions here.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-nodal-trait-regularization: the parent constructs an entire finite resolving tower; this task has a separate fixed local or regular-output input and never supplies that tower. The human explicitly requested its extraction from the long proof.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-persistent-node-normalization: the existing theorem separates persistent generic nodes by normalization and pinching; this task concerns smooth-generic singularities or one point blowup and constructs no normalization.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-point-blowup-fibre-defects: the existing theorem assumes a regular total surface and studies point blowups there; here the centre has nonregular model exponent n>=2, so that hypothesis fails.

lem-sfb-nodal-trait-finite-singular-charts vs lem-sfb-trait-nodal-etale-dvr-model: the existing normal form supplies pointed charts including the smooth-generic clause; it gives no global finite singular set or dimension bounds and proves no comparison of reduced-point blowups.

lem-sfb-nodal-point-blowup-local-descent vs def-sfb-surface-point-blowup-data: the existing node defines centre ideals, exceptional fibres and transform chains; it proves none of the geometric assertions of this task.

lem-sfb-nodal-point-blowup-local-descent vs lem-sfb-common-nodal-model: the existing theorem compares two marked possibly smooth-generic-failing models; it gives neither a finite singular-chart analysis of one family nor the local point-blowup comparison required here.

lem-sfb-nodal-point-blowup-local-descent vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing theorem computes explicit arithmetic charts and their pullbacks. This task must still isolate the two reduced scheme-theoretic centres, obtain Cartesian comparisons covering every point above x and descend to an arbitrary X; it is not just the displayed chart computation.

lem-sfb-nodal-point-blowup-local-descent vs lem-sfb-nodal-log-dualizing-pullback: the existing theorem concerns logarithmic dualizing line pullback along a given nodal modification; it proves none of the finite-chart or exceptional-fibre assertions here.

lem-sfb-nodal-point-blowup-local-descent vs lem-sfb-nodal-trait-regularization: the parent constructs an entire finite resolving tower; this task has a separate fixed local or regular-output input and never supplies that tower. The human explicitly requested its extraction from the long proof.

lem-sfb-nodal-point-blowup-local-descent vs lem-sfb-point-blowup-fibre-defects: the existing theorem assumes a regular total surface and studies point blowups there; here the centre has nonregular model exponent n>=2, so that hypothesis fails.

lem-sfb-nodal-point-blowup-local-descent vs lem-sfb-trait-nodal-etale-dvr-model: the existing normal form supplies pointed charts including the smooth-generic clause; it gives no global finite singular set or dimension bounds and proves no comparison of reduced-point blowups.

lem-sfb-nodal-point-blowup-local-descent vs lem-trf-module-strict-transform-flat-pullback: the existing theorem compares module strict transforms under an already given flat blowup square, not reduced-point isolation, nodal descent or residual singularities.

lem-sfb-nodal-point-blowup-projective-fibres vs def-sfb-surface-point-blowup-data: the existing node defines centre ideals, exceptional fibres and transform chains; it proves none of the geometric assertions of this task.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-per-excellent-normalized-blowup-tower: the existing statement concerns geometry of finite normalized point-blowup towers, with the stated smooth/regular/excellent or normalized-blowup hypotheses. This task allows a nonregular arithmetic nodal centre over an arbitrary DVR and additionally computes the connected geometric exceptional fibre; those hypotheses and conclusions are not supplied by the existing node.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement concerns normalized blowups preserve quasi-projectivity over an excellent affine base, with the stated smooth/regular/excellent or normalized-blowup hypotheses. This task allows a nonregular arithmetic nodal centre over an arbitrary DVR and additionally computes the connected geometric exceptional fibre; those hypotheses and conclusions are not supplied by the existing node.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-per-integral-blowup-projective-geometry: the existing theorem assumes X integral and gives integrality and projective-bundle projectivity; it gives neither finite-space H-projectivity nor exceptional-fibre connectedness for a possibly disconnected X.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-per-normalized-blowup-tower-etale-descent: the existing statement concerns descent and projectivity of finite normalized blowup towers, with the stated smooth/regular/excellent or normalized-blowup hypotheses. This task allows a nonregular arithmetic nodal centre over an arbitrary DVR and additionally computes the connected geometric exceptional fibre; those hypotheses and conclusions are not supplied by the existing node.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-per-regular-point-blowup-acyclic: the existing statement concerns geometry and first-direct-image vanishing of a regular point blowup, with the stated smooth/regular/excellent or normalized-blowup hypotheses. This task allows a nonregular arithmetic nodal centre over an arbitrary DVR and additionally computes the connected geometric exceptional fibre; those hypotheses and conclusions are not supplied by the existing node.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-per-surface-point-blowup-geometry: the existing statement concerns regularity and projectivity of a point blowup on a regular surface, with the stated smooth/regular/excellent or normalized-blowup hypotheses. This task allows a nonregular arithmetic nodal centre over an arbitrary DVR and additionally computes the connected geometric exceptional fibre; those hypotheses and conclusions are not supplied by the existing node.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-common-nodal-model: the existing theorem compares two marked possibly smooth-generic-failing models; it gives neither a finite singular-chart analysis of one family nor the local point-blowup comparison required here.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-integral-blowup-projective-geometry: the existing theorem assumes X integral and gives integrality and projective-bundle projectivity; it gives neither finite-space H-projectivity nor exceptional-fibre connectedness for a possibly disconnected X.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-nodal-log-dualizing-pullback: the existing theorem concerns logarithmic dualizing line pullback along a given nodal modification; it proves none of the finite-chart or exceptional-fibre assertions here.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-nodal-trait-regularization: the parent constructs an entire finite resolving tower; this task has a separate fixed local or regular-output input and never supplies that tower. The human explicitly requested its extraction from the long proof.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-point-blowup-fibre-defects: the existing theorem assumes a regular total surface and studies point blowups there; here the centre has nonregular model exponent n>=2, so that hypothesis fails.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-projective-affine-base-blowup: the existing theorem gives only H-projectivity for a finite-type ideal; it does not establish this point ideal is finite type, compute geometric exceptional fibres or prove their connectedness and nonempty-fibre preservation.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-sfb-trait-nodal-etale-dvr-model: the existing normal form supplies pointed charts including the smooth-generic clause; it gives no global finite singular set or dimension bounds and proves no comparison of reduced-point blowups.

lem-sfb-nodal-point-blowup-projective-fibres vs lem-trf-smooth-center-blowup-geometry: the existing theorem has a smooth ambient scheme and smooth centre over Q; the arithmetic nonregular point here satisfies neither hypothesis.

lem-sfb-regular-trait-curve-surface-components vs base-change-dimension: the existing theorem preserves dimensions of curves under algebraically closed field extensions; this task is about total-space dimension-two components over a DVR.

lem-sfb-regular-trait-curve-surface-components vs def-sc-discrete-valuation-ring: the existing statement concerns discrete valuation rings and uniformizers. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs def-weil-pbc-cohen-ring: the existing statement concerns cohen ring. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-exc-punctured-curve-branches: the existing statement concerns the punctured strictly local curve has dvr branches. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-pc-dimension-affine-open-cover: the existing theorem computes dimension from an affine cover; it gives no proper-flat specialization, clopen decomposition or vertical DVR.

lem-sfb-regular-trait-curve-surface-components vs lem-pc-scheme-dimension-local-rings: the equality with a supremum is an input, but the existing theorem does not obtain the lower bound two on each component or identify any vertical stalk.

lem-sfb-regular-trait-curve-surface-components vs lem-per-normal-surface-exceptional-curves: the existing theorem assumes an excellent integral normal surface and a birational morphism and treats contracted curves; no such morphism or excellence is assumed here.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-dvr-galois-components-stalk-principal: the existing statement concerns principal maximal ideal of a normalized finite galois component stalk. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-dvr-normalized-compositum-local-diagram: the existing statement concerns compatible local dvr diagram of a finite normalized compositum. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-dvr-uniformizer-root-algebra: the existing statement concerns a dvr after adjoining a positive-order root of a uniformizer. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-dvr-unit-root-at-prime: the existing statement concerns dvr and separable residue extension at a unit-root prime. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-regular-cartier-generic-stalk-dvr: the existing local theorem requires an integral effective Cartier centre; the special fibre here may be reducible and its individual component is not supplied with a Cartier centre structure. This task also proves the global dimension-two decomposition and identifies pi as uniformizer.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-regular-principal-prime-localization-dvr: the existing statement concerns a regular principal-prime localization is a dvr. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-root-cover-generic-pullback: the existing statement concerns the generic root-cover model is a pullback. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sbc-root-normalization-stalk-principal-ideal: the existing statement concerns the normalized root stalk maximal ideal is principal independently of ramification. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sc-dvr-dimension-one: the existing statement concerns a discrete valuation ring has dimension one. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sc-dvr-field-extension-order: the existing statement concerns a dvr keeps its normalized order after extending its residue field. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sc-dvr-saturation-line-smith-normal-form: the existing statement concerns smith normal form for a submodule of a finite free pid module. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sc-normal-dim1-dvr: the existing statement concerns one-dimensional normal local rings. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sc-smooth-connected-curve-local-rings: the existing statement concerns smooth connected curves: integral, local rings at closed points are dvrs. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sfb-dvr-matrix-smith-powers: the existing statement concerns rectangular smith matrices over a dvr. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sfb-dvr-scalar-tor: the existing statement concerns tor of finitely presented dvr modules and cyclic power quotients. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-sfb-regular-point-blowup-functions: the existing statement concerns regular functions under a regular point blowup. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-trf-smooth-component-pure-transcendental: the existing theorem gives geometric integrality of a smooth field-scheme component with a purely transcendental point; this task is a regular proper-flat scheme over a trait, with no such point hypothesis.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-cohen-completion-dvr: the existing statement concerns the completion of a flat local p-adic algebra with maximal ideal (p) is a dvr. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-completion-of-dvr-is-dvr: the existing statement concerns the completion of a discrete valuation ring is a discrete valuation ring. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-dvr-completion-regular: the existing statement concerns characteristic-zero dvr completion is a regular map. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-dvr-unit-times-uniformizer-power: the existing statement concerns in a dvr every nonzero element is a unit times a power of a uniformizer. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-geonormal-dim-one-smooth: the existing theorem concerns geometrically normal dimension-at-most-one field schemes; it does not apply to dimension-two total components over a trait.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-normalization-projective-components: the existing theorem concerns components of a normalization of a projective scheme over a field, not a given regular total space over a trait and its special generic DVRs.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-pid-noetherian-normal: the existing statement concerns a principal ideal domain is a noetherian normal domain. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-principal-maximal-dim-one-regular: the existing statement concerns a one-dimensional local domain with principal maximal ideal is regular. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-regular-local-dim-one-iff-normal: the existing statement concerns a noetherian local ring of dimension one is regular iff it is a normal domain. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-serre-criterion-normal: the existing statement concerns serre's criterion for normality. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs lem-weil-pbc-z-localizations-dvr: the existing statement concerns localizations of the integers are fields or discrete valuation rings. It gives no finite clopen integral decomposition of a proper flat regular trait scheme, no proof that each component meets both fibres and has dimension two, and no identification of pi as the vertical-stalk uniformizer. Its algebraic hypotheses are not assumed for an arbitrary total stalk here; establishing them is part of this task.

lem-sfb-regular-trait-curve-surface-components vs rem-pc-regular-normal: normal clopen integral components are an input to this task, but this existing statement gives no dimension-two conclusion, trait specialization or pi-generated vertical DVR stalks.

## Retained mathematical proof, assigned to the four new tasks

### Original step 1 — lem-sfb-nodal-trait-finite-singular-charts

The DVR $R$ is Noetherian. Finite presentation gives finite type by forgetting the relations in each finite algebra presentation. Hence $X$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. The first-Fitting singular subscheme $N$ of [lem-trf-nodal-family-fitting-singular] is closed and has exactly the nonsmooth locus as underlying set. Its generic fibre is empty by smoothness of $X_K$ and the base-change clause of that lemma. Its special fibre is unramified by [lem-weil-pbc-unramified-base-change-open], so [lem-trf-unramified-field-fibre-decomposition] makes it a disjoint union of spectra of finite separable extensions of $k$. This union is finite: $N$ is a closed subspace of the quasi-compact space $X$, is supported in $X_k$, and the one-point open components of the disjoint union cover it. Thus the nonsmooth points form a finite set of closed special-fibre points. This argument needs no connectedness of any fibre.

Uses: def-sc-discrete-valuation-ring, def-sbc-locally-finite-presentation, lem-weil-pbc-finite-type-over-noetherian, lem-trf-nodal-family-fitting-singular, lem-weil-pbc-unramified-base-change-open, lem-trf-unramified-field-fibre-decomposition.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, first paragraph; curves.tex Tag 0C59 and morphisms.tex Tag 02G7 for finiteness of the nodal set"}.

### Original step 2 — lem-sfb-nodal-trait-finite-singular-charts

At any nonsmooth special-fibre point $x$, apply [lem-sfb-trait-nodal-etale-dvr-model] to obtain $(U,u)\to(X,x)$ and $(U,u)\to(W,w)$ over $S$, with $W$ one of the two displayed models over $R'$. The zero-parameter model cannot occur at $u$: its nodal section $a=b=0$ has generic point specializing to $w=(\pi,a,b)$. The image in $W$ of any open neighbourhood of $u$ is open by [def-weil-etale-morphism, lem-weil-pbc-flat-lfp-open], so contains that generic point. Thus $U_K$ would have a point etale over the origin of $K'[a,b]/(ab)$, a nonsmooth node. The pointwise equivalence of smoothness in [lem-trf-etale-source-smoothness], applied to both etale maps, contradicts smoothness of $X_K$. Consequently we have the model $ab=\pi^n$, with $n\geq1$ since $x$ is nonsmooth. Here $w$ is its origin: outside $a=b=0$ the equation eliminates the other variable and is smooth. This conclusion is also exactly the smooth-generic clause of [lem-sfb-trait-nodal-etale-dvr-model], which supplies at the nonsmooth point $x$ a diagram whose model is $ab=\pi^n$ with $n\geq1$; the argument above only explains why that clause holds.

Uses: lem-sfb-trait-nodal-etale-dvr-model, def-weil-etale-morphism, lem-weil-pbc-flat-lfp-open, lem-trf-etale-source-smoothness.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, first paragraph after the local diagram: exclusion of ab=0 (the omitted detail); Tag 0CDD"}.

### Original step 3 — lem-sfb-nodal-trait-finite-singular-charts

Apply [lem-sfb-dvr-nodal-chart-blowup-calculus] to these pointed models, using its stated invariance under a common pointed etale neighbourhood. A point of $X$ outside the nonsmooth locus has a smooth $R$-neighbourhood of pure relative dimension one, so is regular. At a nonsmooth point with model $ab=\pi^n$, regularity holds exactly for $n=1$. Thus all nonregular points lie in the finite set of step 1, and a nonregular point has $n\geq2$. Also every local ring of $X$ has dimension at most two and every closed point of $X_k$ has local dimension two, by the smooth-case and model-case assertions of that same node. These conclusions apply equally to every later nodal family with smooth generic fibre.

Uses: lem-sfb-dvr-nodal-chart-blowup-calculus.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tags 0CDE and 0CDC: regularity off the nodal set and criterion n>=2"}.

### Original step 4 — lem-sfb-nodal-point-blowup-local-descent

Choose a nonregular $x$ and the diagram of step 2, with $n\geq2$. Shrink $U$ about $u$ so that $u$ is the sole point over $x$ and the sole point over the origin $w$ of $W$. To justify this shrinking, first choose an affine neighbourhood of $x$ in $X$ and an affine neighbourhood of $u$ mapping into it. Both targets (this affine open and $W$) are affine, hence quasi-separated, so the two fibres are quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence] and are disjoint unions of spectra of separable fields by [def-weil-etale-morphism, lem-weil-pbc-unramified-base-change-open, lem-trf-unramified-field-fibre-decomposition]. Hence they are finite reduced sets of closed points, and deleting the other points does the job. Both scheme-theoretic inverse images of the reduced centres are then precisely the reduced point $u$. Let $X^+=\operatorname{Bl}_xX$, $U^+=\operatorname{Bl}_uU$, and $W^+=\operatorname{Bl}_wW$. By [thm-nagata-blowup-flat-base-change] for the comparison of [def-nagata-blowup-flat-base-change-map], both squares with common upper-left object $U^+$ are Cartesian. Their horizontal maps remain etale by [lem-weil-pbc-etale-scheme-base-change].

Uses: lem-weil-pbc-qcqs-morphism-permanence, def-weil-etale-morphism, lem-weil-pbc-unramified-base-change-open, lem-trf-unramified-field-fibre-decomposition, thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map, lem-weil-pbc-etale-scheme-base-change.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, second paragraph: isolating the reduced centre and the two Cartesian blowup squares; Divisors Tag 0805"}.

### Original step 5 — lem-sfb-nodal-point-blowup-local-descent

The three charts of $W^+$ are those in [lem-sfb-dvr-nodal-chart-blowup-calculus]: the two outer charts have equations $at=\pi$ and $bt'=\pi$, and the middle chart has $rs=\pi^{n-2}$. They have nodal geometric fibres over $R'$. They are nodal over $R$ as well: the image of the fixed uniformizer of $R$ is a uniformizer of $R'$ (step 2), so each displayed chart is the etale base change of the identical chart over $R$; apply [lem-weil-pbc-etale-scheme-base-change] and the forward direction of [lem-trf-nodal-family-etale-source-locality]. The map $U^+\to X^+$ covers every point above $x$, since it is the base change of $U\to X$ and its fibre above $x$ contains $\operatorname{Spec}\kappa(u)\to\operatorname{Spec}\kappa(x)$. Together with the open complement of that fibre these maps are an etale cover. Away from $x$ the blowup is an isomorphism by [thm-nagata-global-blowup-complement]. The reverse direction of [lem-trf-nodal-family-etale-source-locality] therefore proves $X^+\to S$ flat and locally finitely presented, with nodal geometric fibres.

Uses: lem-sfb-dvr-nodal-chart-blowup-calculus, lem-weil-pbc-etale-scheme-base-change, lem-trf-nodal-family-etale-source-locality, thm-nagata-global-blowup-complement.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, second paragraph: preservation of nodal fibres; Tags 0CDC, 0C5D"}.

### Original step 6 — lem-sfb-nodal-point-blowup-local-descent

For $n=2$ the middle chart is $rs=1$ and is regular; for $n=3$ it is $rs=\pi$ and is regular too. If $n\geq4$, the only nonregular point of $W^+$ is the middle origin with local equation $rs=\pi^{n-2}$, and its residue field equals that of $w$, by [lem-sfb-dvr-nodal-chart-blowup-calculus]. Over the single point $u$, its inverse image in $U^+$ is consequently a single point with residue field $\kappa(u)$: the Cartesian square makes that fibre the base change of this rational point. All other points of $U^+$ above $u$ are regular by the same node. The common pointed etale criterion in that node and surjectivity above $x$ then show that $X^+$ has exactly one nonregular point above $x$ when $n\geq4$, and none when $n=2,3$. In the former case it has a common pointed etale neighbourhood with the model of exponent $n-2$. Away from $x$ no new nonregular point occurs.

Uses: lem-sfb-dvr-nodal-chart-blowup-calculus, thm-nagata-global-blowup-complement.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, last paragraph, with the correct stopping threshold n=2 or 3; Tag 0CDC"}.

### Original step 7 — lem-sfb-nodal-point-blowup-projective-fibres

The ideal of the reduced closed point is quasi-coherent and of finite type: on a Noetherian affine neighbourhood it is a finitely generated maximal ideal, and away from the point it is the unit ideal. By [lem-sfb-projective-affine-base-blowup], both $X^+\to X$ and $X^+\to S$ are H-projective. In particular they are proper by [lem-kun-projective-implies-proper]. Properness supplies finite type and hence quasi-compactness by [def-weil-proper-morphism, def-weil-finite-type-morphism]; separatedness gives quasi-separatedness by [lem-pc-separated-quasi-separated]; with the local finite presentation from step 5 this is finite presentation by [def-sbc-locally-finite-presentation]. The finite-type-over-Noetherian conclusion of [lem-weil-pbc-finite-type-over-noetherian] also makes $X^+$ Noetherian, so these hypotheses persist at every subsequent step.

Uses: lem-sfb-projective-affine-base-blowup, lem-kun-projective-implies-proper, def-weil-proper-morphism, def-sbc-locally-finite-presentation, lem-weil-pbc-finite-type-over-noetherian, def-weil-finite-type-morphism, lem-pc-separated-quasi-separated.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, projective refinement; Divisors Tag 02NS and Morphisms Tag 01WC"}.

### Original step 8 — lem-sfb-nodal-point-blowup-projective-fibres

Off the centre, every fibre of $X^+\to X$ is a point. Over the centre, base change to $\kappa(u)$ identifies the exceptional fibre with the exceptional fibre of $W^+$ after the corresponding residue extension, by the Cartesian squares in step 4. By [lem-sfb-dvr-nodal-chart-blowup-calculus] its geometric fibre is a projective line for $n=2$, or two projective lines meeting at one point for $n>2$. Either is nonempty and connected: each projective line is connected and the two have a common point. An algebraic closure of $\kappa(x)$ contains an embedding of the finite separable extension $\kappa(u)$, so this computes the geometric fibre of $X^+\to X$ itself. For an arbitrary field extension $k'/\kappa(x)$, connectedness of the fibre after base change to $k'$ then follows from connectedness after base change to an algebraically closed extension, by [lem-weil-geometrically-connected-algebraic-closure]; a fibre $\operatorname{Spec}\kappa(y)$ off the centre stays one point after any field extension. Thus the morphism has nonempty geometrically connected fibres everywhere. In particular it is surjective, and the nonemptiness of all geometric fibres of the family over $S$ is preserved.

Uses: lem-sfb-dvr-nodal-chart-blowup-calculus, lem-weil-geometrically-connected-algebraic-closure.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDC, exceptional fibres of the three blowup charts; Tag 0CDE Cartesian squares"}.

### Original step 9 — item assembly

Fix a nonregular point with chosen exponent $n\geq2$. Induct on $\lfloor n/2\rfloor$ to remove it and its descendants. For $n=2$ or $3$, steps 4--8 give one permissible blowup and no nonregular point over it. For $n\geq4$ they give exactly one remaining nonregular point, with pointed exponent $n-2$; repeat the construction there and use the inductive hypothesis, since $\lfloor(n-2)/2\rfloor=\lfloor n/2\rfloor-1$. The same pointed diagram pulls back at each repetition after the shrinking of step 4. Thus at most $\lfloor n/2\rfloor$ blowups remove the selected point without changing any other original nonregular point. Now induct on the finite number of nonregular points of step 3. Zero points requires zero blowups; otherwise the preceding finite tower reduces their number by one and the outer induction applies. This gives a finite tower ending in a regular $T$. Projectivity, flatness, finite presentation, nodality, nonemptiness and the fibre properties follow at each arrow from steps 5, 7 and 8.

Uses: .

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE, last paragraph: the two nested inductions, with the n=3 case made explicit"}.

### Original step 10 — item assembly

All chosen centres are nonregular points, hence special-fibre points by step 3. Each blowup is an isomorphism off its centre by [thm-nagata-global-blowup-complement], so the composite is an isomorphism on the generic fibre. It is also an isomorphism over the original relative smooth locus: initially that locus is regular by step 3; inductively its inverse image is still isomorphic to it and hence regular, so no subsequent nonregular centre lies there. This proves both isomorphism clauses without assuming that all special-fibre nodes must be blown up.

Uses: thm-nagata-global-blowup-complement.

Source: {"document": "literature/stacks-project/models.tex", "place": "Tag 0CDE: all centres are singular closed points; complement isomorphism for each blowup"}.

### Original step 11 — lem-sfb-regular-trait-curve-surface-components

By [rem-pc-regular-normal], the regular Noetherian scheme $T$ is a finite disjoint union of integral normal open-and-closed components $T_i$; each is regular because its local rings are local rings of $T$. The dimension bounds of step 3 apply to $T$: all local dimensions are at most two, and closed points of $T_k$ have dimension two. Every $T_i$ meets the generic fibre: if it did not, its nonzero integral local rings would have $\pi=0$, contradicting flatness over $R$. Here multiplication by the nonzero element $\pi$ is injective after tensoring $0\to R\xrightarrow{\pi}R$ with a flat local ring, using the injectivity definition in [def-weil-pbc-flat-ring-map]. Since $T\to S$ is proper, the image of the closed subset $T_i$ is closed by [def-weil-proper-morphism]. It contains the generic point, so also the closed point of $S$. Choose a closed point in the nonempty Noetherian special fibre of $T_i$. Its local dimension is two. The equality between scheme dimension and the supremum of local dimensions in [lem-pc-scheme-dimension-local-rings] now gives $\dim T_i=2$. Thus these components are precisely integral regular surfaces.

Uses: rem-pc-regular-normal, def-weil-flat-morphism, def-weil-proper-morphism, lem-pc-scheme-dimension-local-rings, def-weil-pbc-flat-ring-map.

Source: {"document": "literature/stacks-project/models.tex", "place": "Properties Tags 033M and 04MU; Tag 0CDC local dimension bounds and Tag 0CDE regular output"}.

### Original step 12 — lem-sfb-regular-trait-curve-surface-components

Let $\xi$ be the generic point of a special-fibre component of $T$. The reduced nodal special fibre has field local ring at its generic point. Consequently, for $A=\mathcal O_{T,\xi}$, the quotient $A/\pi A=\mathcal O_{T_k,\xi}$ is a field, so its maximal ideal is $(\pi)$. The ring $A$ is a Noetherian local domain by regularity and [rem-pc-regular-normal]. Flatness makes $\pi$ nonzero in $A$, by the injectivity argument of step 11. Hence [lem-sc-principal-ideal-dvr] applies and makes $A$ a DVR. No excellence or completion of $R$ was used anywhere.

Uses: rem-pc-regular-normal, lem-sc-principal-ideal-dvr.

Source: {"document": "literature/stacks-project/models.tex", "place": "Algebra Tag 00PD, principal-maximal-ideal characterization; Tag 0CDE regular nodal output"}.

## Retained returned report (historical; the existing:true rebind below is withdrawn)

## Worker report

Existing declaration: `AlgebraicGeometry.exists_nodal_trait_regularization` in
`Sheaf.AlgebraicGeometry.NodalTraitRegularization`, already present in the live
repository and recorded as independently reviewed for NS on 2026-10-22.
The dispatch brief expected an unstated node, but this node is now stated.
This delivery records `existing: true`; it introduces no Lean module and changes
only `lean`. Its signature is extracted verbatim from the existing source.

Source read: Stacks Project models.tex, lemma-blowup-at-worst-nodal (0CDE),
and its explicit reference to the blowup charts of example-blowup (0CDC).
The existing theorem's docstring contains the node's twelve proof steps, with
its sources and dependency references. Its proof is still `sorry`, as required
for stage 2.

Clause-by-clause correspondence:

- DVR: `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  Fraction field: `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`.
  Base scheme: `Spec (.of R)`; the residue point is `IsLocalRing.closedPoint R`,
  with its canonical residue field supplied by the scheme fibre construction.
- Family: `(X : Scheme.{u}) (f : X ⟶ Spec (.of R))`.
  Projectivity is `[IsHProjective f]`, flatness `[Flat f]`, local finite
  presentation `[LocallyOfFinitePresentation f]`. H-projectivity implies properness,
  hence quasi-compactness and quasi-separatedness, so finite presentation is fully
  present without extra assumptions.
- Nonempty reduced pure-one-dimensional geometric fibres: `hfib` quantifies over
  algebraically closed fields `Ω : Type u` and all `g : Spec Ω ⟶ Spec R`, imposing
  `Nonempty`, `IsReduced`, and `Scheme.IsPureDimension 1` on `pullback f g`.
- Ordinary nodes: `hnodal` quantifies over closed points not in the smooth locus
  of `pullback.snd f g` and requires the maximal-ideal adic completion of the
  stalk to be ring-isomorphic to `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`.
  The model and its complete local ring are the ones in the node. Over an
  algebraically closed ground field, the usual ring-isomorphism criterion for
  an ordinary double point is the recorded nodal convention.
- Smooth generic fibre: the `Smooth` instance on `pullback.snd f
  (Spec.map (CommRingCat.ofHom (algebraMap R K)))`.
- Finite tower: existential `m : ℕ`, `Y : Fin (m+1) → Scheme`, initial isomorphism
  `e₀ : Y 0 ≅ X`, arrows `b j : Y j.succ ⟶ Y j.castSucc`, and maps `p` to `X`.
  `p 0 = e₀.hom` and `p j.succ = b j ≫ p j.castSucc` make `p (Fin.last m)`
  the displayed composite, rather than an unrelated morphism.
- Each arrow is the specified blowup: existential closed point `x` and isomorphism
  `e` to `(Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowup`, with
  `e.hom ≫ ...blowupMap = b j`. The vanishing ideal gives the reduced induced
  scheme structure. `¬ IsRegularLocalRing (...stalk x)` gives nonregularity.
- Every centre is special: `(p j.castSucc ≫ f) x = IsLocalRing.closedPoint R`.
- Each arrow is proper with nonempty geometrically connected fibres:
  `IsProper (b j) ∧ GeometricallyConnected (b j)`.
  Mathlib's latter predicate uses `ConnectedSpace`, which includes nonemptiness.
- Every stage: `IsHProjective (p j ≫ f)`, `Flat`, `LocallyOfFinitePresentation`,
  `QuasiCompact`, `QuasiSeparated`, and the same nonempty/reduced/pure-dimension
  and completed-nodal-local-ring conditions on every geometric fibre.
  Here nonsmoothness is expressed by absence of a smooth open neighbourhood,
  the definition of the smooth locus used in `hnodal`.
- Terminal regularity: `IsRegularScheme (Y (Fin.last m))`.
- Generic-fibre isomorphism: `IsIso (pullback.snd (p (Fin.last m))
  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))`.
  This is the base change of the actual composite along `X_K ⟶ X`.
- Isomorphism over the original relative smooth locus:
  `IsIso (p (Fin.last m) ∣_ f.smoothLocus)`.
- Finite disjoint union of integral regular surfaces: existential `n` and open
  pieces `U : Fin n → T.Opens`, each closed, pairwise disjoint, with supremum `⊤`,
  and `IsIntegral`, `IsRegularScheme`, `topologicalKrullDim = 2` on each piece.
  These clopen pieces give exactly the asserted disjoint union.
- Special-component generic-point local rings are DVRs: for every
  `Z ∈ irreducibleComponents` of the special fibre and every `IsGenericPoint ξ Z`,
  the stalk in the total terminal scheme at `fiberι ... ξ` has an existential
  `IsDomain` instance and `IsDiscreteValuationRing` with that instance.
- No connectedness is imposed on geometric fibres of the intermediate families.

Dependency declarations read and used by the existing theorem:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`.
- `Mathlib.RingTheory.AdicCompletion.Basic` (ring operations in `.Algebra`): `AdicCompletion`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, defined as
  `IsLocallyNoetherian X ∧ IsRegular X`, including the node's local-Noetherian condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  the connected companion of def-pc-geometrically-irreducible is
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`,
  explicitly imported in the existing module. The node's record itself notes this.

Edge cases checked: zero blowups (`m = 0`) are allowed; an already regular family
need not be altered. A special-fibre node with regular total ring (`xy = π`)
is not forced to be a centre. The `xy = π²` and `xy = π³` models stop after one
blowup, whereas higher exponents decrease by two as the proof explains. Empty
geometric fibres are explicitly excluded; pure dimension alone would not exclude
them. Disconnected fibres and multiple terminal integral components are allowed.
No perfection, excellence, completeness, characteristic restriction, or splitness
assumption is added. All field/scheme universes use the common `u`, so tests include
algebraic closures of residue fields; the theorem does not quantify over a universe
smaller than the base. All variables and universe parameters are explicitly bound.

Searches made (2026-10-22):

- `msearch.py leanfinder`: "Regularization of a projective flat nodal curve over a
  discrete valuation ring by blowups of nonregular closed points". Eight Mathlib
  hits about Weierstrass minimal models/reduction; none is this general theorem.
- `msearch.py loogle`: `AlgebraicGeometry.exists_nodal_trait_regularization`.
  Unknown identifier in the Mathlib search index, no hits.
- `msearch.py grep`, Mathlib AlgebraicGeometry:
  `nodal.*regulariz|regulariz.*nodal|exists_nodal_trait_regularization`, no hits.
- `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `exists_nodal_trait_regularization`, and `nodal.*regulariz` found the exact
  existing module and its theorem at line 215, and consumer references in
  `CommonMarkedNodalModel.lean`. No upstream duplicate was found.

No statement correction, missing notion, dependency repair, or disputed statement.
The expected dispatch state was stale; the one-definition-per-notion instruction
requires reusing the already landed theorem.

Validation: the delivery wrapper checks the existing declaration on the server via
an isolated module-mode import and `#check`; the dry run also runs maintainer preflight.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
