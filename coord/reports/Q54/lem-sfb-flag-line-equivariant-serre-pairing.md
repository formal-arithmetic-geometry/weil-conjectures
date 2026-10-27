# Q54 stage-1 delivery: lem-sfb-flag-line-equivariant-serre-pairing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flag-line-equivariant-serre-pairing.json — item, statement, split into six steps; mathematical statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-proper-coherent-trace-pairing.json — new statement-only node; no Mathlib match. This is general coherent Serre duality for arbitrary smooth proper schemes and locally free sheaves, with its geometric trace naturality. It has no flag varieties, roots or representation-theoretic hypotheses.
- report.md and citations.json — report and verbatim statement excerpts for every proof-step citation.

One new node, zero Mathlib leaves. No Lean, compilation, or repository/launcher modifications.

## Attachments

None. Searched the project by the item tag, equivariant Serre pairing, canonical bundles and duality. The curve declarations AlgebraicGeometry.Scheme.exists_trace_perfect_cupPairing (WeilConjectures/AlgebraicGeometry/Curve/TracePairing.lean:174) and AlgebraicGeometry.Scheme.serreDuality_residueTrace (Curve/ResidueTrace.lean:383) only concern relative dimension one. The monomial/projective-space pairings are specific to projective space. None states the flag canonical-character and all-degree group-scheme-equivariant result, nor the new arbitrary-dimensional smooth proper theorem with geometric naturality.

## WANTED

WANTED: H. H. Andersen, The strong linkage principle (1980), Lemma 4 proof, printed p.58, for the item's original representation-theoretic application. This was already WANTED in the item's source. No assertion here is justified by pretending to have read that unavailable article: the proof uses locally available Stacks and Milne instead. No additional source is required for the split.

## Corrections and scope

No STATEMENT-DISPUTED issue was found. The item was an unsplit statement; its canonical character, trace, perfectness and all-algebra invariance needed actual arguments. I retained all original fields, citations and search history and added the missing differential/exterior/cohomology/cup-product statement dependencies. The inherited blueprint ancestor is null; blueprint_refs.py ancestor confirmed that fact, so the exact inherited place and via chain were kept, and the new node prepends this item to that via chain. The latest blueprint direct-image proof and unit were read under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. Their current argument does not spell out the historical representation-theoretic prerequisite chain; this delivery supplies the assigned supporting item without changing the chapter or unit.

The split does not move the whole item into another node. The canonical isotropy determinant calculation, extension from torus to Borel, associated-bundle convention, tensor identifications, rational actions, and universal-point argument remain in the item's proof. The new node is a general coherent-duality tool from Stacks, independent of that geometry. It is not a new statement of the flag canonical-line clause. Smooth proper dualizing identification alone does not state a perfect cup pairing or its trace naturality, so the existing relative-dualizing-object nodes cannot replace this tool in one line.

## Searches

I read the inherited Mathlib searches and retained them. For the new node, all searches were made through the required msearch.py and are recorded in searches.jsonl, then copied exactly by tool and query into mathlib_searches. Two LeanFinder formulations searched respectively vector-bundle Serre duality and geometric trace/base-change naturality. LeanSearch returned abstract LinearMap.IsPerfPair facts; Loogle's Serre/dual and cohomology/dual searches had no hits; both grep searches in Mathlib/AlgebraicGeometry had no hits. LeanFinder returned finite-dimensional category evaluation, smooth-ring cotangent modules and algebraic-field/linear-map traces. Reading the returned types shows that none is a trace on coherent sheaf cohomology or the requested duality theorem. No unavailable service is claimed to have proved absence.

Whole-DAG and whole-blueprint searches used Serre duality, smooth proper coherent, coherent duality, canonical bundle, homogeneous, cotangent, trace pairing, duality trace, and the Stacks tags. The general-dimensional theorem is not supplied by the curve or projective-space results. I opened all tag-sharing statements used for the distinctions below. I also read the general proper-flat-space duality node, the smooth-proper relative dualizing node, and the nodal trace-duality node: the former two lack the required cohomological pairing plus differential-normalized trace naturality, and the last is restricted to nodal relative curves.

## Review by Q54

For the item I read Milne, Algebraic Groups (2017), Proposition 7.15 and Remark 7.16(c), printed pp.142--143; 18.9--18.14, pp.389--390; and Theorem 21.11 with Corollary 21.13, pp.428--430, from the locally available PDF. Section 18.13 has exactly the associated-bundle rule (g,z)b=(gb,chi(b^-1)z), so the canonical character has the same convention as the statement. For the new node I read Stacks duality.tex at lemma-duality-proper-over-field (0FVV), remark-duality-proper-over-field (0FVW), lemma-duality-proper-over-field-perfect (0FVY), and remark-rework-duality-locally-free-CM (0FW0), including the discussion of finite-dimensionality and the trace evaluation pairing. I also read lemma-trace-map-and-base-change (0B6J) and lemma-proper-flat-base-change (0AAB), with their trace square and the proper-flat base-change hypothesis. These identify the precise compatibility left to the new unsplit theorem. Its automorphism action uses the differential normalization on omega, not an arbitrary isomorphism with a dualizing object, and its cup pairing uses ordinary evaluation. That normalization is part of the statement so it cannot later be silently chosen differently. The new node has only its statement and searches, not a hidden proof sketch.

Step 1 uses the statement of reductive-borel-pair-structure for semisimple implies reductive, standard-parabolic-levi-charts with I empty for the proper quotient and finitely presented torsor, and homogeneous-cotangent-associated-bundle for smoothness, the exact tangent quotient, exterior compatibility and pure dimension. The torsor node explicitly says finitely presented; I did not infer that hypothesis from a node stating only faithful flatness. B^- is a smooth Borel as required. All three statements were opened and the quoted parts are in citations.json.

Step 2 uses reductive-rank-one-reflections for the full toral/root decomposition and the dimension-one root spaces, and borel-opposite-root-dichotomy for the precise Borel Lie subspace. Subtracting these direct summands computes the quotient; dualizing negates actual torus characters. This is valid in characteristic 2 as well: the calculation never replaces characters by their differentials. Taking a wedge basis proves its determinant in a few lines. It does not invoke a missing flag tangent-weight lemma.

Step 3 uses the rank-one node for root groups isomorphic to Ga, borel-root-product-coordinates for their ordered product parametrization of U^-, reductive-borel-pair-structure for U^- semidirect T, and the homogeneous-cotangent node for the exterior associated line. A Ga character is a unit of F[t], hence constant and equal to 1 at the identity. This proves triviality on U^- as a morphism, with no rational-point density shortcut. The remaining character is therefore -2rho. The associated-bundle rule is explicitly compared with the item's section rule. The elementary flag is for this few-line calculation from the cited structural statements, not for the structural theorems themselves.

Step 4 uses actual regular local sections of the Borel torsor from standard-parabolic-levi-charts, so its tensor/evaluation maps are checked on free bases and on their transition functions. Inverses are on the same bases, and left-translation equivariance is checked on the multiplication map. Linearized-qcoherent-cohomology-coaction supplies rational coactions and base-change evaluation. Its affine-group, finite-type, quasi-compact separated scheme and quasi-coherent sheaf hypotheses all hold: S is affine finite type, Q is proper over F, and the homogeneous lines are locally free. I did not cite a definition of rational action in place of this cohomology theorem.

Step 5 uses the full statement of the new smooth-proper-coherent-trace-pairing node: Q is smooth proper of pure dimension N by steps 1--2; the input sheaf is a locally free line by step 4. The trace is defined by the inverse of the specific equivariant omega identification. Its evaluation pairing is the multiplication pairing computed in step 4, so both perfectness maps and finite-dimensionality are exactly the conclusion cited, with every hypothesis checked. The generic Serre theorem is non-elementary and is not smuggled into an elementary step.

Step 6 uses linearized-qcoherent-cohomology-coaction for the evaluation of a coaction over every A and the new node for trace/cup naturality under A-automorphisms. Applying them to inverse translation matches the left action rather than its inverse convention. The second factor uses the dual linearization and the differential linearization of omega, so it is exactly the dual-tensor line from step 4. Taking A=F[S] and the universal point yields the comodule equalities, hence invariance over every algebra, including nonreduced ones. This avoids treating invariance at F-points as scheme-theoretic invariance.

I checked delivery-errors B--E against the resulting files: all new objects and hypotheses are introduced; definitions are inline or referenced; the single new node is statement-only; the Stacks places are tags and labels; the search entries really ran; every step's cited result was read at its statement, not borrowed from a proof; no step uses a descendant of this item; elementary tensor, determinant and polynomial-unit calculations are steps, not redundant nodes; and all non-elementary input has a cited node. I checked that the proof-dependency list is exactly the union of uses and that every citation quote is verbatim. No step exceeds 2000 characters. No SGA source is used. The general duality statement and coaction assembly carry genuinely separate inputs, and the flag character is actually derived.

Small cases: S trivial gives N=0, Q=Spec F and the multiplication pairing F x F -> F with degree-zero trace. For SL2, including characteristic 2, the positive root is twice the fundamental weight and the result is omega(P1)=O(-2), so the character sign agrees. For SL3, the three positive tangent weights alpha1, alpha2, alpha1+alpha2 have sum 2rho and the canonical line is their negative determinant. The new theorem allows disconnected smooth proper schemes: in dimension zero the trace is the sum of finite-etale algebra traces, not a claimed isomorphism H^0(omega)=k. A zero sheaf or zero cohomology factor produces the zero-to-zero perfect pairing. All k-algebras A are flat over the field; nilpotent A and the zero ring cause no excluded case. These tests exposed no false clause and required no change of statement.

## Not duplicates

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sfb-projective-line-module-serre-duality: the newly landed node gives abstract cohomology-dual isomorphisms for invertible modules on smooth projective schemes, natural only in sheaf morphisms. It states no canonical trace, cup-evaluation formula, compatibility with arbitrary coefficient algebras, or differential-normalized naturality under geometric automorphisms. The new node covers general smooth proper schemes and finite locally free sheaves with exactly those additional trace compatibilities; its use here cannot be a one-line specialization of the existing statement.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-per-rational-surface-gorenstein-blowups: the existing statement concerns point blowups resolving a rational surface singularity to a Gorenstein surface, not smooth proper coherent cohomology pairings.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-per-rational-canonical-trace-generation: the existing statement concerns canonical-module generation under modifications of a rational local surface singularity, not trace pairings on smooth proper schemes over a field.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-proper-flat-right-adjoint-restriction-open: the existing statement is restriction of proper-flat right adjoints to opens, not a perfect coherent pairing.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-self-product-right-adjoint-base-change-local: the existing statement identifies adjoints on a self-product, not a trace or coherent cup pairing.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-smooth-proper-diagonal-basechange-upper-shriek: the existing statement identifies an upper-shriek object on a self-product, without a cohomological trace pairing.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-proper-flat-right-adjoint-basechange-chart: the existing statement is conditional invertibility on affine charts of a right-adjoint base-change map, without a cohomology-pairing conclusion.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-proper-flat-right-adjoint-basechange-global: the existing statement is a conditional global assembly of base-change invertibility from an affine assertion, not a cohomological duality pairing.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-proper-flat-right-adjoint-basechange: the existing statement identifies pullbacks of right-adjoint images in derived categories, without identifying the differential canonical line, its trace, or the cohomological perfect pairing.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sc-derived-open-restriction-detects-iso: the existing statement is a derived-category locality criterion for isomorphisms, with no duality or cohomology-pairing assertion.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sfb-relative-nodal-perfect-duality-trace: the existing statement is relative derived duality for a map between nodal curve families; it does not apply in arbitrary relative dimension or directly identify the smooth canonical determinant trace pairing.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sfb-flag-line-equivariant-serre-pairing: the assigned item identifies the specific homogeneous canonical character and constructs group-scheme equivariant flag-line pairings; the new node has arbitrary smooth proper schemes and locally free sheaves, with no group action or root data.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sfb-proper-adjoint-diagonal-pair: the existing statement constructs a coherent relative dualizing pair and diagonal class; it supplies no canonical differential trace or finite-dimensional cup-product duality theorem.

lem-sfb-smooth-proper-coherent-trace-pairing vs lem-sfb-top-bottom-cohomology-simple-image: the existing statement is a highest-weight/simple-image assertion, using the assigned item; it is not a coherent-duality theorem.

Additional conceptual comparisons: the curve Serre-duality blueprint nodes are restricted to dimension at most one, projective-space pairings to projective spaces, and lem-sc-smooth-proper-relative-dualizing-general states only an object isomorphism, so none states the new theorem. The existing homogeneous-cotangent-associated-bundle is reused directly; no duplicate canonical-line or flag tangent-weight node was created.

## Unfinished work

No part of this one-level split is left unfinished. The single new node is intentionally unsplit, as required by the worker brief. The required server dry run and direct push are the delivery validation; their outcome is recorded below after they run.

## Validation

The required deliver.py --no-push exited successfully with OK (not pushed), commit 7971c26e498. Server preflight, check_dag and review_split passed. After correcting the report-only ResidueTrace line reference to 383, the final dry run is repeated before pushing.

During the first push the duplicate-tag gate detected a concurrent landing, lem-sfb-projective-line-module-serre-duality. I opened its complete statement and source and added the explicit comparison above. Its naturality in E does not imply the needed geometric automorphism/trace compatibility by direct specialization. The delivery is revalidated after this report-only repair.
