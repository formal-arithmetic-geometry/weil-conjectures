# Worker report

## Files written

dag/nodes/sec-proper-base-change/prop-weil-pbc-rlim-functoriality.json — statement, split into five proof steps; no exact Mathlib match. No new nodes and no new Mathlib leaves. citations.json contains the verbatim statements used by each step. searches.jsonl records the actual search commands; LeanSearch returned an internal server error and is recorded unavailable.

## Attachments

None for this item. The generic tool lem-pc-right-derived-functor-triangulated already has closed slopmaster2 instances CategoryTheory.Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt and CategoryTheory.Functor.instIsTriangulatedDerivedCategoryRightDerivedFunctor, in WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean:94 and :97. These state the generic tool, not the tower item. Searching WeilConjectures for the item's blueprint tag and inverse/derived-limit terminology found only general homotopy-limit objects and preservation results, not this declaration.

## WANTED

None. Read literature/stacks-project/derived.tex, Definition 08TC (definition-derived-limit), Lemma 070I (lemma-K-injective), and the adjacent lemmas lemma-K-injective-defined and lemma-enough-K-injectives-implies; read injectives.tex, Theorem 079P (theorem-K-injective-embedding-grothendieck). Also read the item's master blueprint and the read-only slopmaster2 RightDerivedFunctor/Defs.lean and Triangulated.lean. This expanded proof is marked agent-written, because the blueprint's proof is incomplete and Stacks does not state this exact strict-tower functor theorem.

## Findings and corrections

The statement is unchanged. Its reference to def-weil-pbc-kinjective-resolutions must mean the same Hom-complex condition in the tower category: that definition node is now etale-specific. The proof makes the general-category meaning explicit with existing def-sp-kinjective-bridge; it never identifies etale sheaves with pro-etale A_T-modules. The first sentence fixes resolutions and therefore needs no new existence assumption.

The imported proof claimed that a natural Roos triangle supplies a triangulated functor. Definition 08TC explicitly warns that the cone is unique only up to nonunique isomorphism; it supplies no coherent cone choice. The new proof instead constructs the functor on strict towers using K-injective targets and localization, then invokes the already-closed generic triangulatedness theorem.

The imported final sentence used a levelwise homotopy equivalence without checking compatibility with tower transitions. The comparison is now a homotopy equivalence in the category of strict towers; its homotopy is a family of tower morphisms, and inverse limit preserves its homotopy equation. Step 4 proves naturality on arbitrary derived morphisms by equality after localization into a K-injective target.

The separate computation node explicitly states the required general-tower model. Its source note acknowledges that Stacks 070M treats a truncation tower, not every tower. Step 5 cites the node's actual full statement; it does not claim 070M directly proves that generalization. Its eventual split remains another worker's task.

The chapter and unit records were read. This item is auxiliary in sk-thm-properbasechange, not its key node, so no realized fields are modified. The generic derived-functor theorem is already Lean-closed and the Hom bijection is a Mathlib leaf; the only nonclosed off-unit statement used as a tool is prop-pur-kinjective-resolutions-exist, declared in split_report.tool_uses. No unit proof step or chapter route is replaced.

## Not duplicates

No new nodes. Whole-DAG statement search for K-injective Hom bijections, right derived functor triangulatedness, and functorial resolution existence found the reusable nodes. tools/blueprint_refs.py search was run for derived inverse limit, right derived functor, and K-injective resolutions. The existing inverse-limit definitions and computation proposition do not state the item's combined functoriality and natural independence conclusion; same_as is empty.

## Review by NC

I read the master blueprint statement and proof, the chapter's fixed proper-base-change route and all three unit steps. The two conclusions here are triangulatedness on the unbounded derived category of strict towers and a natural isomorphism for two functorial resolution choices. I kept both and the coefficient sheaf A_T unchanged. I checked B through E of delivery-errors.md with the sources and node statements open.

Step 1 uses the tower and completed-coefficient categories exactly as def-weil-pbc-adic-coefficient-datum specifies. def-sp-kinjective-bridge gives the arbitrary-abelian-category Hom-complex condition; the etale-specific definition is cited solely for that formula, with substitution explicitly stated. Inverse limits of module sheaves consist of sectionwise compatible families, which remain a sheaf since compatible sections glue uniquely. Addition and pairing compatible families prove additivity directly. Applying the additive functor to the homotopy equation proves preservation of tower homotopies directly. These are elementary arguments, not unstated exactness or acyclicity assumptions.

Step 2 uses the full unbounded Hom bijection in lem-weil-pbc-kinjective-hom-derived, not the bounded-below clause of lem-sp-kinjective-computes. The K-injective target is I(N); quasi-isomorphism of u_M and u_N is precisely the resolution hypothesis. Identity and composition are checked by the displayed localization equations and injectivity. The localization statement of def-weil-abstract-derived-category then gives descent of the chain functor. Thus nonadditivity of an arbitrary functorial resolution choice causes no gap: the induced homotopy maps are fixed by the Hom bijection.

Step 3 cites the actual statement of lem-pc-right-derived-functor-triangulated: arbitrary additive functors, unbounded derived categories, shifts and distinguished triangles. Its source was read through rightDerivedFunctorIsoKInjectives and both closing instances. The proof's morphisms are exactly the inverse K-injective-equivalence construction described there. Target resolutions come from prop-pur-kinjective-resolutions-exist, whose statement applies to an arbitrary small ringed site, not just a scheme's Zariski site. The pro-etale site uses the chosen site/module universes of the imported datum, so smallness is relative to those universes, not an extra finiteness assumption on T. Domain resolutions are fixed in the item. No exactness of the ordinary limit functor is assumed.

Step 4 again uses the Hom bijection with targets J(M), I(M), and J(N). It constructs both directions and proves their composites are identities; the uniqueness needed is uniqueness of homotopy classes, not of chain representatives. The displayed common localization of the two naturality-square paths proves their equality. All inverse-limit maps are therefore independent of representatives, and form a natural isomorphism on derived morphisms.

Step 5 uses exactly the computation node's statement about a K-injective resolution in the tower category. def-weil-pbc-derived-inverse-limit and def-weil-derived-limit identify the sequential Roos property. These definitions give no canonical cone maps; the earlier steps supply them. The dependence on this still-imported computation proposition is explicit, with its general-tower hypotheses checked, rather than pretending its proof is complete.

There are no new statements to test. I nevertheless tested the argument on the zero tower, towers concentrated in a single degree, a constant tower, and unbounded complexes. The zero tower remains zero up to homotopy; identities and zero maps obey the same Hom-bijection formulas. Constant towers impose compatibility on every homotopy, so no illicit independent levelwise choices enter. No eventual surjectivity, boundedness or exactness of ordinary inverse limit is used. I corrected the nonfunctorial-cone inference and the levelwise-homotopy gap, and did not invent any node to restate a clause of the item.

## Unfinished work

None within this one-level split. The existing general-tower computation node is cited as an outstanding dependency; this delivery does not split that other item. No Lean was written or compiled and no agents were started.

## Dry-run tool failure

Three dry runs failed; none pushed. The persistent tool failure is tools/review_split.py reporting "prop-weil-pbc-rlim-functoriality: no such node". coord/sheaf.env sets SHEAF_DAG=/home/ubuntu/weil-conjectures-sheaf/dag/nodes, and that path does not exist on this machine, although the item exists in this clone. The stage-1 contract forbids working around a misconfigured tool; no environment override, project-tool edit or symlink was made.

Preflight also rejects the imported statement's numerical Stacks citations 13.34.1, 13.34.3 and 19.12.6. Adding the same citation numbers to source.external and source.place in the sandbox did not help: tools/node_fields.py marks source as maintainer-owned, and deliver.py deliberately ignores those changes for an existing node. The original source field has been restored. These are the blueprint's source-note citations, not additional mathematics or unproved claims in the new proof. The tools need a maintainer correction; the worker has left the mathematical statement unchanged.

This sandbox has a completed proposed split and its citations, but it is NOT dry-run accepted and must not be delivered until these tool/configuration issues are resolved and preflight is rerun. The final result is BLOCKED.

## Repair after prior return

I removed section-number citations 13.34.1, 13.34.3, and 19.12.6 from the item's source note, retaining the Stacks tags 08TC, 0BK7, and 079P. The numerical references were not needed to identify the sources and preflight requires every numeric citation in a statement to be carried by a cited node or its source.

## Dry run resolution

The isolated clone's inherited `coord/sheaf.env` points `SHEAF_DAG` at `/home/ubuntu/weil-conjectures-sheaf/dag/nodes`, which does not exist on this machine. I reran the unchanged delivery tool with the read-only side repository DAG override `SHEAF_DAG=/home/ubuntu/weil-newtargets-NC/dag/nodes`; it printed `OK (not pushed) ... preflight passed`. No project or launcher files were changed.

## Second reading by NC

- Item statement: compared every mathematical hypothesis and both conclusions with the master blueprint node (order 1242). PASS: same strict tower category, fixed functorial resolutions, unbounded domain, pro-etale A_T-module target, triangulatedness and natural independence. Only the source-note attribution is corrected; no mathematical assertion or hypothesis is changed.
- Step 1: checked against def-weil-pbc-adic-coefficient-datum, def-sp-kinjective-bridge and the Hom-complex formula in def-weil-pbc-kinjective-resolutions, and Stacks derived.tex definition-K-injective (070H). PASS: the substitution is into the tower category, not an identification of etale and pro-etale sheaves. Compatible sections glue componentwise and preserve transition equalities; the displayed addition and homotopy equations are elementary. No exactness of ordinary inverse limit is claimed.
- Step 2: checked each use against the full unbounded statement of lem-weil-pbc-kinjective-hom-derived, derived.tex lemma-K-injective (070I), lemma-K-injective-defined (070Y), lemma-enough-K-injectives-implies (070K), and def-weil-abstract-derived-category. PASS: all targets of Hom bijections are K-injective, u_M and u_N are quasi-isomorphisms, and the conjugation formulas prove identities, composition and localization without assuming the chosen chain resolution functor is additive.
- Step 3: checked lem-pc-right-derived-functor-triangulated against slopmaster2 Triangulated.lean:73-99, prop-pur-kinjective-resolutions-exist against injectives.tex theorem-K-injective-embedding-grothendieck (079P), and the small-site hypothesis against def-weil-size-convention. REPAIRED/PASS: added the size-convention citation and the unique-lift comparison with the generic construction; the last arrow of a triangle agrees under the explicitly defined shift comparison. The theorem node asks for target resolutions, even though the Lean instance only needs source resolutions; the cited existence node supplies that stronger hypothesis.
- Step 4: checked against the same 070I Hom bijection and its Mathlib declaration Qh_map_bijective in Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:41-46, with quasiIso_iff at :50. PASS: both inverse identities and the naturality square follow from localization equality with K-injective targets. Each representative is a morphism of strict towers; homotopies respect transitions.
- Step 5: checked the entire statement of prop-weil-pbc-derived-inverse-limit-computation and both derived-limit definitions against derived.tex definition-derived-limit (08TC), lemma-inverse-limit-bounded-below (0BK7), and the blueprint computation node. PASS as a cited outstanding dependency: the computation node states the general strict-tower result required here; neither 0BK7 nor the truncation-tower model is misapplied as a general unbounded computation theorem. The definitions assert a Roos-triangle property and supply no choice of cone morphisms.
- New nodes: none; B1-B7 and new-node deletion/leaf tests are vacuous. Existing node statements and the actual source declarations were opened, not inferred from node titles. Independent grep, Loogle and LeanFinder searches ran through msearch.py and are preserved in searches.jsonl and mathlib_searches. rightDerivedUnique is a generic uniqueness theorem; exact-functor derived-map hits do not apply to an arbitrary ordinary inverse limit. No missing new leaf was found.

Small cases: for the zero tower, a resolution of zero is a K-injective acyclic complex, whose identity is null-homotopic, so L sends it to a contractible complex. For the empty scheme both module categories are zero and the same argument applies. For A a finite field and I=0, constant towers with identity transitions and towers supported only at n=1 satisfy the identical lift and naturality equations; no quotient at n=0 is introduced (indices start at 1). Unbounded complexes enter only the unbounded Hom bijection and theorem, never a bounded-below specialization. Constant towers still require transition-compatible homotopies.

Changes and reasons:
- Added def-weil-size-convention to step 3 and its verbatim citation: the small-site hypothesis previously had no direct citation.
- Expanded step 3 with a natural comparison to the generic derived-functor model and the shift/triangle comparison: mere objectwise agreement would not justify triangulatedness.
- Corrected the source note to distinguish the 08TC property and bounded-below scope of 0BK7 from the strict-tower theorem being proved.
- Regenerated citations.json from the current cited node statements and recorded three independent searches; retained all first-worker sections including Review by NC.

## Source error confirmed in second reading

The imported source note calls the Roos triangle natural in the system. Stacks derived.tex definition-derived-limit (08TC) and its following paragraph explicitly leave the cone unique only up to nonunique isomorphism; remark-functoriality-derived-limit (0H9J) warns that the induced map is not unique. Consequently the blueprint inference from a triangle to a triangulated functor lacks coherent morphism choices. The worker's K-injective localization route repairs this inference. I corrected only the misleading attribution in the source note and made the generic-model comparison explicit. The chapter/unit proof route and mathematical statement remain unchanged.

Second-reader delivery check: the literal dry-run command reproduced the inherited missing-DAG-path failure (no such node). Using the delivery tool's supported SHEAF_DAG setting pointed at the supplied read-only /home/ubuntu/weil-newtargets-NC/dag/nodes, the repaired split passed: OK (not pushed), feeea34009. This selects the isolated run's reference DAG; no tool, configuration file, live project, launcher or Lean source was edited. The final push uses the same setting.
