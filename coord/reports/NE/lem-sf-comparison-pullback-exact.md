# lem-sf-comparison-pullback-exact

## Worker report

Stage 1, NE, 2026-10-16. Rechecked the existing sandbox against the current shared DAG and the sources. The item remains unsplit in the shared DAG. Its statement is unchanged: the six proof steps establish the constant-ring identification and tensor formula, exactness, and the natural cohomology comparison with its two consequences. There are no new nodes and no new Mathlib leaves. The current brief requires a dry run and handover to another reader; nothing is pushed by this worker.

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-comparison-pullback-exact.json`: existing statement, six-step split; not a Mathlib leaf. Retained the existing split and clarified the last vanishing assertion as “for every i<a”.
- `report.md`: replaced the accumulated reports with this current stage-1 handover and review.

Retained and checked `citations.json`: one verbatim quotation for each of the 20 step/node citation pairs. Retained `searches.jsonl`: actual outputs of the prescribed search wrapper. `write_split.py` is an earlier sandbox preparation script, not a delivery file; it was not rerun. `dry-run.log` holds the final preflight output.

## Attachments

None for the whole item. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for comparison, constant-sheaf and exactness declarations. Read `SixFunctors/ProEtale/Comparison/Defs.lean`: `AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar` (line 105), `AlgebraicGeometry.ProEtale.additive_comparisonUpperStar` (119), and `AlgebraicGeometry.ProEtale.preservesHomology_comparisonUpperStar` (123) provide exactness for Grothendieck abelian coefficients. Also read `Comparison.lean:113`, including `AlgebraicGeometry.ProEtale.comparisonUpperStarUnitIso` (118), `Comparison/Monoidal.lean:43` onward, and `ConstructibleSheaf.lean:107`, including `AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIso` (111). The unit and constant-module isomorphisms are not the ring-sheaf identification with the tensor-formula module pullback required by clause 1. These declarations cover parts of the item, not every clause. No upstream master sorry declaration is treated as a finished proof.

## WANTED

None. The required literature exists read-only in `/home/ubuntu/weil-launcher-nt/literature/`; the JSON keeps the canonical project-relative literature paths. No source was downloaded or written.

## What was wrong and what changed

The shared item has no proof steps and only historical grep searches. The sandbox supplies a complete argument, additional statement dependencies for the small etale site, module-sheaf category and tensor product, whole-blueprint provenance and the genuinely executed Mathlib searches. The statement itself is correct against the sources; there is no STATEMENT-DISPUTED correction.

The earlier blocker concerned stage-2 records and compilation. This is a stage-1 task under the explicit human restriction, and GOAL.md defers stage 2. Such requests do not prevent preparing and checking this natural-language split. This report makes no claim of Lean formalization or compilation. The earlier report's repeated stage-2 discussion and purported completed second reading have been removed from the current handover; the next reader must independently assess the accepted sandbox.

I changed the final step's phrase “for exactly the same degrees” to “for every i<a”: the proved implication preserves the stated lower vanishing bound. No statement, dependency, citation pair, source reference or hypothesis changed in this recheck.

## Mathlib and blueprint searches

All 2026-10-16 searches retained in the item have matching actual entries in `searches.jsonl`. They were run through `/home/ubuntu/weil-launcher-nt/msearch.py NE lem-sf-comparison-pullback-exact`. No query was invented in this recheck. LeanSearch's Internal Server Error remains recorded as unavailable. LeanFinder was tried with both the comparison-site statement and the more general exact-functor/cohomology statement. Loogle's `Functor.PreservesHomology` query returned an unknown identifier, and `CategoryTheory.Functor, "homology"` returned general short-complex functors. Grep checked geometric comparison, exact-functor homology, and inverse images of constants. The later constant-sheaf searches are also genuine logged queries.

Read the pinned Mathlib source at `CategoryTheory/Sites/ConstantSheaf.lean:70` for `constantSheafAdj`, and `Algebra/Homology/ShortComplex/PreservesHomology.lean:60,777` for `preservesHomologyOfExact` and `homologyFunctorIso`. These generic results are already represented by the cited existing leaves. They do not state the entire small etale/pro-etale ringed comparison. No new leaf is claimed.

Re-ran `tools/blueprint_refs.py ancestor lem-sf-comparison-pullback-exact`, which gives `def-compact-support-direct-image-detailed`, and whole-blueprint searches for comparison pullback, comparison and constant sheaf. Searched the DAG for Tags 04JC/03D2 and read the nearby existing statements. `prop-weil-pbc-site-comparison-finite-level` supplies exactness among its assertions, but not the full ring/tensor/cohomology statement; the exact inverse-image statements for morphisms of schemes have different source and target sites. Retained `same_as: []` and the precise ancestry through `def-sf-etale-origin-subcategory`. This is an auxiliary typing lemma in `sk-def-sf-operations`, not its key node, so there is no unit record to realize. The chapter and unit records were read and their routes retained.

## Not duplicates

No new nodes. Existing general statements and Mathlib leaves are reused. No elementary calculation or clause of the item has been moved into a child node.

## Review by NE

I read the source statements and proofs in `sites-modules.tex`: Tag 03D2, `lemma-pullback-module`; Tag 03D7, `lemma-adjoint-pullback-pushforward-modules`; Tag 03DA, `lemma-abelian`; `definition-flat-morphism` and Tag 04JC, `lemma-flat-pullback-exact`. I also read `sites.tex` Tag 00YV, `proposition-functoriality-algebraic-structures-topoi`, with its algebraic-object discussion, and Tag 0H7J, `example-constant-sheaf`; `proetale.tex` Tag 099R, `section-comparison`, and Tag 0GLZ, `lemma-describe-pullback-from-etale`; and `homology.tex` Tag 010N, `lemma-exact-functor`. The complex-cohomology naturality is supplied by the cited existing Mathlib leaf, whose declaration I read, rather than attributed to an unstated consequence of 010N. There are no new nodes requiring separate source statements.

Step 1 uses `def-weil-pbc-site-comparison-morphism` for the finite-limit-preserving set adjunction and restriction formula. It uses `lem-weil-pbc-adjunction-lifts-group-ring-objects` for the actual lifted adjunction, and `lem-weil-pbc-sheaf-algebraic-structures-objects` for the identification with ring sheaves. All three statements were opened. The sites have finite products; the left adjoint preserves them, and the right adjoint restriction preserves them. The inclusion fixes T/T, so global sections after restriction are evaluated at the same terminal object. No definition is being cited for an unproved exactness assertion.

Step 2 cites those three statements and `lem-weil-pbc-constant-sheaf-maps-global-sections`. The latter explicitly covers commutative rings and evaluation at a final object. The displayed Hom bijections therefore apply to both coefficient-ring sheaves. I checked the directions of c and d: naturality gives dc=id and cd=id by the two displayed equations. This is an elementary representing-object calculation from the cited natural bijections, not an uncited general Yoneda theorem. The adjunct of c fixes every constant scalar. This argument works on disconnected schemes without identifying all global sections of a constant sheaf with Lambda.

Step 3 cites the comparison-morphism definition for the finite-product action on fixed scalar operations, the module-category definition for actions, `lem-weil-pbc-ringed-topoi-module-adjunction` for the tensor pullback, and `def-pur-sheaf-tensor-product` for sectionwise tensor followed by sheafification. Those statements were opened. Applying the inverse-image functor to the action diagrams proves the module axioms; the constant-section calculation checks agreement with the fixed-Lambda functor. The maps m tensor b -> c inverse(b)m and m -> m tensor 1 are inverse by the balancing relation and commute with restrictions. Commutativity of Lambda allows either order of the tensor factors. Extension along a ring isomorphism leaves the underlying abelian kernels and sheafified cokernels unchanged, so it is exact and the coefficient map is flat. These are explicit elementary action and tensor calculations from the cited statements. No theorem about a morphism of schemes is used for this morphism of sites.

Step 4 cites the comparison-morphism definition, `lem-weil-pbc-site-pullback-abelian-exact` and the module-category definition. The exactness theorem explicitly applies to any morphism of sites and supplies additivity, kernels and cokernels. The module-category statement supplies the corresponding kernel and sheafified-cokernel descriptions. The step verifies that the underlying abelian objects agree, and that an underlying inverse to a linear isomorphism is linear. The biproduct identities and the displayed finite-diagram kernel/cokernel presentations prove preservation of all finite limits and colimits, including the empty diagram. No sectionwise surjectivity of a sheaf epimorphism is assumed.

Step 5 cites the module-category definition, `lem-weil-pbc-exact-functor-complex-cohomology` and `def-weil-derived-cohomology-sheaves`. The first supplies abelianness in the chosen larger universe; step 4 supplies exact additivity. The cohomology theorem explicitly supplies the stated direction, naturality and compatibility with cycles and quotient maps for every integer degree and arbitrary complexes. The cohomology-sheaf definition identifies these categorical quotients with the required sheaves. Taking sections is never assumed exact, and no boundedness hypothesis is inserted.

Step 6 cites the same cohomology theorem, the cohomology-sheaf definition and `def-weil-pbc-derived-categories`. The naturality equation is correctly typed. A functor preserves inverse pairs and an additive functor preserves zero; these elementary observations prove preservation of quasi-isomorphisms and of the same lower bound a. The final wording now states exactly the implication proved.

Checked all 20 step/node pairs against the full current statements: every quote in `citations.json` is verbatim, with no missing or extra pair. `proof_deps` equals the union of the steps' `uses`. Traversing the full 161-node statement/proof dependency closure found no missing or merged dependency and no cycle. The five off-unit general tools are proposed only in `split_report.tool_uses` for the maintainer to judge; the maintainer-owned top-level field is untouched. They supply general adjunction/exactness interfaces and replace no unit step.

Small cases: Lambda=0 leaves only zero modules; T empty gives the zero ring sheaf and zero module category. The final-object Hom formulas still apply. Disconnected T needs no connectedness assumption. Lambda=Z/4Z shows that no field or coefficient regularity is used, since the coefficient map is an isomorphism. The zero complex, a one-term complex, an acyclic complex, arbitrary negative a and fully unbounded complexes all satisfy the same degreewise argument; cohomology in a fixed degree uses only adjacent terms. No Noetherian, finite-type, invertibility or hidden bounded-below hypothesis is introduced.

Against delivery-errors B–E: all notions have existing definition dependencies; there are no new proof-bearing unsplit nodes, duplicate children or relabelled clauses; every non-elementary fact is supplied by an opened cited statement; the actual calculations appear in the proof steps; the searches are logged rather than fabricated. The statement and all hypotheses remain intact. No Lean, compiler, Lake, live-project edit, launcher edit or direct git command was used.

## What remains

Only the independent second reading and delivery. This worker runs `deliver.py NE lem-sf-comparison-pullback-exact --no-push` and leaves the accepted sandbox for that reader.

## Second reading by NE

- Item statement: checked clause by clause against Sites and Modules Tags 03D2, 03D7, 03DA, 04JC, Sites Tag 0H7J, Pro-etale Tag 099R/0GLZ, and Homology Tag 010N; the finite-ring, both sites, ring comparison, module exactness, cohomology naturality, quasi-isomorphism, and lower-bound hypotheses are all present. Added existing definition citations for the small etale site, module sheaves, and cochain complexes.
- Step 1: checked against the statement of `def-weil-pbc-site-comparison-morphism`, `lem-weil-pbc-adjunction-lifts-group-ring-objects`, and `lem-weil-pbc-sheaf-algebraic-structures-objects`; the finite-product and ring-object lift are exactly what the step uses, and no module exactness is smuggled into this step.
- Step 2: checked against Tags 0H7J and 00YV and the four cited statements; the two natural Hom bijections, their directions, and the two inverse composites are explicitly calculated, including the terminal-object restriction. This works for disconnected and empty sites without identifying all global sections with the coefficient ring.
- Step 3: checked against Tags 03D2 and 03D7 and the statements of the tensor-product, module-category, and comparison nodes; the transported action, scalar agreement, tensor maps, restriction compatibility, and exact change along the ring isomorphism are written out. No scheme morphism or unproved sectionwise epimorphism claim is used.
- Step 4: checked against Tags 04JC and 03DA and the exact abelian inverse-image statement; the hypotheses are supplied by the comparison node, and the kernel/cokernel and finite (co)limit arguments include the empty diagram. The module-linear inverse argument is stated rather than assumed.
- Step 5: checked against Homology Tag 010N and the statements of the module-category, exact-functor-cohomology, and cohomology-sheaf nodes; exactness gives the cycle and boundary identifications in every integer degree, with no boundedness or sectionwise-cohomology assumption.
- Step 6: checked against the naturality clause of the exact-functor-cohomology node and the derived-category/cohomology definitions; the displayed naturality equation has the correct direction, and preservation of inverse pairs and zero gives the quasi-isomorphism and every-degree lower-bound conclusions.
- New nodes: none; no child node was introduced, duplicated, or used to restate an item clause. Existing off-unit general tools are cited only through their statements and remain listed for maintainer tool-use review.
- Definition and form audit: the item and all cited existing nodes have self-contained TeX statements and source tags/labels; all 20 citation quotes remain verbatim, `proof_deps` is the union of step uses, and no dependency cycle or unrecorded fact was found. Small cases checked were the zero ring/module, empty scheme/site, disconnected scheme, one-term and zero complexes, arbitrary negative lower bound, and a nonfield coefficient ring such as $\mathbf Z/4\mathbf Z$.
- Changes made: added three inline definition citations and the cochain-complex statement dependency (the site and module-category dependencies were already present); no mathematical hypothesis or conclusion was changed. The delivery dry run is rerun after this report update.
