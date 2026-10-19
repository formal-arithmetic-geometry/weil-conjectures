# Stage-1 report: det-pe-condensed-point-coefficients

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-condensed-point-coefficients.json` — statement split; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/det-pe-condensed-point-topology.json` — new unsplit statement node; no Mathlib match.
- `citations.json` — verbatim citations for all proof-step uses.

## Attachments

None. No finished declaration tagged `(blueprint: det-pe-condensed-point-coefficients)` occurs in the slopmaster2 source.

## WANTED:

None.

## Not duplicates

- `det-pe-condensed-point-topology` vs existing DAG nodes: no existing node states the geometric-point cover criterion or the resulting equivalence with condensed sets; `lem-weil-pbc-comparison-sections` has a different affine evaluation statement and is cited instead.

## What I checked and changed

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the worker role and delivery-errors sections B–E, `SETUP.md`, `coord/dag-sync.md`, and `GOAL.md`. I copied the imported item and checked the current blueprint statement and proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-condensed-point/`. I searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its concepts, and the blueprint tag; no completed declaration exists. The item now restores all statement dependencies used by its clauses and proof, including the existing comparison-sections node and the pulled-back-coefficients definition. The topology dependency is self-contained and explicitly cites the affine basis, pro-etale site, and condensed-ring site definitions in its statement.

## Review by Q72

For step 1 I read `sk-def-sfb-pullback-from-point`, `det-pe-condensed-point-basis`, and the new topology node. The first supplies the inverse-image adjunction and its right adjoint on test objects; the basis node identifies the test object with `\\Omega[S]`; the topology node states that restriction along this functor is an equivalence. These statements give the natural evaluation isomorphism, with ring compatibility obtained by the stated monoidal structure and finite-product naturality. I checked the separably closed hypothesis and the specialization `X=Spec \\Omega`.

For step 2 I read `sk-def-sfb-condensed-ring`, `det-pe-condensed-point-basis`, `lem-weil-pbc-comparison-sections`, the new topology node, and `sk-def-sfb-pulled-back-coefficients`. The condensed-ring statement gives continuous sections; the basis statement gives `LC(S,\\Omega)` and the finite-quotient presentation; the comparison-sections statement gives the filtered-colimit evaluation formula; the topology node gives agreement on the affine basis; and pulled-back coefficients supplies the notation `A_X`. The compact-to-discrete argument was written explicitly as continuous maps being locally constant, and the empty profinite set and zero ring are included by the same formulas. Every step citation has a quote in `citations.json` that is a verbatim part of the cited statement and is long enough for the delivery checker.

I ran all required `msearch.py` searches for the item and the new topology node, including LeanFinder/LeanSearch, Loogle, and Mathlib grep with second phrasings. The semantic hits were generic condensed or étale-cover declarations and no exact theorem; Loogle's unknown identifiers are recorded as unavailable. The topology node was checked against the full blueprint topology statement and proof, with no SGA source used. The server-side `srvcheck.py ... review_split` returned `PASS`, and `deliver.py Q72 det-pe-condensed-point-coefficients --no-push` returned `OK (not pushed)` after preflight.

## What was wrong in the imported material

The earlier sandbox item had narrowed `stmt_deps` and proof uses despite using the comparison-sections and pulled-back-coefficients statements. Its topology citation was only in proof text, and the topology statement did not identify the site notions it used. I restored the complete dependency/use sets, made the topology statement cite its defining nodes, and replaced a too-short adjunction quote with the full clause from `sk-def-sfb-pullback-from-point`. The dry run initially caught these issues; the final dry run passed.

## What I could not finish

No mathematical or mechanical part remains unfinished. The split is ready for the second reader; I did not deliver or push it.

## Second reading by Q72

This section supersedes the first reader's description of the final file set and proof: the delivered split has only the item file, no new nodes, and six proof steps. I read the current main-20261015 coefficient statement and both proof paragraphs, the geometric-point unit, and the topology statement and its Points/Coverings/Topoi proof. The item statement is unchanged, including separably closed (not algebraically closed), all condensed sets and rings, arbitrary topological rings, and arbitrary discrete rings. Its finite quotients are explicitly specified in Step 4.

- Step 1: checked against det-pe-condensed-point-basis clauses (2)–(3), the evaluation-prime formula of lem-weil-pbc-locally-constant-prime-spectrum, the arrow-permanence clause of lem-weil-pbc-ind-etale-stability, and the exact affine-open covering definition in def-weil-pbc-proetale-site; PASS. Read Stacks proetale.tex Tags 097M (lemma-ind-etale-permanence), 097N (lemma-ind-etale-implies), and 0989 (definition-fpqc-covering). The existing spectrum theorem works for every field, not only algebraically closed fields. Pulling an affine open of the affine target back to an affine source is an affine fibre product, so the converse covering argument meets the condition for every affine open.
- Step 2: checked the full-faithfulness clause of det-pe-condensed-point-basis, all four clauses of lem-weil-pbc-ind-etale-basis, and every hypothesis of lem-pc-fppf-dense-sheaf-equivalence against Mathlib/CategoryTheory/Sites/DenseSubsite/SheafEquiv.lean:107; PASS. The cover-dense basis and the topology calculation in Step 1 supply the actual hypotheses, and def-weil-size-convention supplies smallness; sets and abelian groups in the larger universe have the required limits.
- Step 3: checked the complete adjunction clause of sk-def-sfb-pullback-from-point and the geometric inverse image in lem-weil-pbc-profinite-point-pullback against the archived master RefactorInstruction.tex Section 4, lem:XS and prop:pX, and the current coefficient definition sk-def-sfb-pulled-back-coefficients; REPAIRED. The first citation alone stated only the abelian adjunction although the item also quantifies over sets. The additional existing geometric-morphism node supplies the set inverse image; the composite right adjoint is explicitly evaluated. The unit of an equivalence gives the section isomorphism. Its naturality at the ring operations and finite-product projections explicitly checks the ring structure; no commutativity is imposed.
- Step 4: checked the definitions of continuous sections and pulled-back coefficients in sk-def-sfb-condensed-ring and sk-def-sfb-pulled-back-coefficients; REPAIRED. The finite clopen image partition proves factorization through a finite quotient, and a common refinement proves injectivity of the colimit formula. Precomposition proves naturality, rather than a claim of unspecified transport. Compactness is used only for the finite-image assertion when the coefficient ring is discrete.
- Step 5: checked the inverse-limit test-object formula in sk-def-sfb-pullback-from-point, the finite-stage clause of det-pe-condensed-point-basis, and the complete representability statement of lem-galois-constant-sheaf-sets-representable; REPAIRED. Read Stacks etale-cohomology.tex Tag 03P5 (remark-constant-locally-constant-maps) and sites.tex Tag 0H7J (example-constant-sheaf). Each component of the finite étale scheme is Spec Omega; its map to the disjoint-copy constant scheme chooses a single label. Componentwise gluing establishes ring operations and precomposition establishes every transition map. This supplies the formerly unstated equality A_{X,Et}(Spec Omega^{S_i}) = A^{S_i}.
- Step 6: checked lem-weil-pbc-comparison-sections in the DAG and its complete source statement/proof in the master blueprint, and the extension/detection clauses of lem-weil-pbc-ind-etale-basis; REPAIRED. The base X is affine and each U_i is affine étale of finite presentation; for noncommutative A the comparison is applied to its underlying abelian sheaf, a Z-module sheaf, then the canonical restriction maps preserve the ring operations. Basis uniqueness extends both inverses and the operation identities. The final constant-sheaf conclusion is now proved by the universal property of def-weil-pbc-constant-sheaf: glue constants over finite clopen fibres, and use u(*) = X. It is not inferred merely from an equality of unrelated section sets.
- New node det-pe-condensed-point-topology: checked every clause against the current blueprint topology statement/proof and searched all DAG chapters with blueprint_refs.py search and direct key-word searches; REMOVED. Its spectrum clause is a specialization of the existing closed lem-weil-pbc-locally-constant-prime-spectrum; its cover criterion is the direct affine-open calculation in Step 1; and its topos clause is the existing basis theorem plus the Mathlib dense-subsite comparison in Step 2. No separate statement obligation is needed. The existing geometric-field-profinite-dense-subsite and geometric-field-proetale-evaluation nodes were also read and deliberately not substituted: both assume an algebraically closed field, a stronger hypothesis than this item.

Edge cases: S empty and finite stages of cardinality zero give the empty scheme and the one-element section ring; the empty covering covers exactly the empty scheme. For S a singleton the functor gives X and the displayed evaluations give T and A. The zero coefficient ring has exactly one section on every test object. Finite two-point sets give coordinatewise products and restrictions, checking the orientations of all maps. No perfectness, characteristic-zero assumption, algebraic closedness, nonempty-space assumption, or commutativity of a general discrete ring was used.

Independent searches: I ran msearch.py with a new LeanFinder phrasing about an equivalence between the small pro-étale site of an algebraically closed field and profinite spaces, Loogle query `"Profinite", "Sheaf"`, Mathlib grep `pro.?etale|ind.?etale|weakly.?etale` under AlgebraicGeometry, and LeanSearch about the small pro-étale site of a separably closed field. All services returned successfully. I read the relevant actual sources: Mathlib AlgebraicGeometry/Sites/Proetale.lean defines the site but gives no such equivalence; Condensed/Equivalence.lean compares profinite and compact-Hausdorff sites, not a scheme site; CategoryTheory/Sites/Coherent/Equivalence.lean transfers an already supplied category equivalence. They do not state the item. These searches are recorded as returned in searches.jsonl and summarized in the item's mathlib_searches. Source checkouts were searched by the item id and the geometric-point/profinite concepts; no sorry-free slopmaster2 declaration states this separably closed coefficient theorem. No Mathlib leaf or Lean attachment was added.

Changes and reasons:

- Removed the unnecessary topology node and replaced its black-box citation with the existing spectrum, ind-étale permanence, basis and dense-subsite comparison statements, with the covering calculation written out.
- Expanded the set-valued adjunction, operation compatibility, finite-quotient colimit, finite-stage constant evaluations and final constant-sheaf universal property, repairing the missing justifications described above.
- Retained the original item statement and all first-worker report sections; added the existing set-valued pullback and constant-sheaf definitions to statement dependencies.
- Regenerated citations.json with one verbatim cited statement per step use, so the hypotheses remain visible. No new nodes or Mathlib leaves remain.

The generic tool uses from other units are lem-weil-pbc-ind-etale-stability (arrows in the basis are weakly étale), lem-weil-pbc-ind-etale-basis (the existing realization of the blueprint's affine-basis input), lem-weil-pbc-profinite-point-pullback (the set-valued version of the same test-object inverse image), lem-galois-constant-sheaf-sets-representable (only finite-stage constant sections), and lem-weil-pbc-comparison-sections (the blueprint's affine evaluation input). These supply the same unit route, not a different geometric-field argument. They are declared in split_report.tool_uses for the maintainer to judge; the maintainer-owned tool_uses field is not written.

Validation: the required `deliver.py Q72 det-pe-condensed-point-coefficients --no-push .` completed successfully on 2026-10-17, returning `OK (not pushed)` and `preflight passed` at dry-run commit 3f28441a7e. No local DAG checker, preflight, compiler, Lake or build command was run.
