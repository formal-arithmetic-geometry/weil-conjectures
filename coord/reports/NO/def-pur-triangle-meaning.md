# Worker report: def-pur-triangle-meaning

## Files written

- `dag/nodes/sec-smooth-purity/def-pur-triangle-meaning.json`: existing definition, split; preserve its statement verbatim and reuse existing notions. No new nodes and no Mathlib leaves.
- `citations.json`: `[]`, since a definition has no proof steps.
- `report.md`: replacement report for the returned delivery.

## Attachments

None. Searching the read-only `WeilConjectures/` source by the item tag, declaration names and compatibility concepts found no project declaration defining all three clauses on the pro-etale support triangle. `AlgebraicGeometry.Etale.supportLocalizationTriangle` and its cone comparison in `SixFunctors/OpenClosed/Supports.lean:157,169` construct an etale triangle; they neither define these three compatibility meanings nor cover the pro-etale coefficient setting of the current prerequisite.

## Wanted sources

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-pur-triangle-meaning.md`, node/order 1932, for def-pur-triangle-meaning.

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-pur-support-triangle.md`, node/order 1931, for its existing prerequisite.

The blueprint source files are not installed in this shared checkout. I read their imported statements in the DAG, the chapter record and the unit record, rather than claiming to have opened absent files. The item is a definition, so there is no substitute proof to attribute to an unavailable document. No downloads or literature edits were made.

## Returned-delivery repair

The return reports that landing timed out on `coord/.merge.lock`; it asks for a rebase onto the current DAG, a reread of changed citations, adjustment, and redelivery. The authorized first-worker workflow here ends with a dry run: a second reader pushes. `deliver.py --no-push` constructs its commit from the current upstream baseline in a temporary worktree; no manual git command was run.

I reread every statement dependency in the current shared DAG, particularly the reviewed `def-pur-support-triangle`, whose dependencies now use the general ringed-site K-injective definition and existence theorem instead of the older etale-only resolution interface. Its statement fixes the bounded-below complex and chosen resolution with injective terms, and gives the support complex, inclusion and cone differential. Its support convention is pro-etale. This change in prerequisite scope invalidates the old report's reliance on sandbox etale Lean wrappers as evidence for this item.

The repair keeps `def-weil-etale-morphism` and adds `def-pc-base-change` and `def-weil-proetale-inverse-image` as explicit statement dependencies. The first defines the etale hypothesis, the second defines the two displayed fibre products, and the third defines the pro-etale module pullback appearing as v^*K (applied degreewise to complexes). The scheme-property collection remains the existing convention reference. These are existing definitions, not new lemmas or alternative proof routes. The stale sandbox-only `lean` metadata was removed from the node copy; it did not exist on the current shared item and is not stage-1 evidence. Old Lean files and build artifacts already in this sandbox were left untouched and were not compiled or delivered.

The imported statement itself is unchanged: no statement dispute, new hypothesis, theorem claim or weakening is introduced. The definition says what compatibility means; it does not assert that the three compatibilities hold. Their proof belongs to `lem-pur-support-localization-triangle`, not to this node.

## Review by NO

I reread `coord/brief-stage1.md`, stage 1, the three levels in SETUP, GOAL, dag-sync, and delivery-errors B through E. I also read the current chapter and `sk-prop-a1-kummer` unit record: this definition supplies language for the support-localization auxiliary construction and does not replace a step of the affine-line/Kummer route. This item is not the unit's key statement, so no unit realization field is changed.

For canonicality, the current support prerequisite supplies a chosen K-injective resolution; the item defines independence under derived comparison maps. It does not silently require literal equality of resolutions or prove their comparison. For functoriality, morphisms of complexes and the derived category come through that prerequisite's `def-weil-abstract-derived-category` dependency. The clause requires the specified triangle map to respect composition. For etale compatibility, `def-weil-etale-morphism` states that an etale map is locally of finite presentation, flat and unramified. `def-pc-base-change` states that scheme base change is the fibre product with its two projections. `def-weil-proetale-inverse-image` explicitly defines the small pro-etale inverse image and the module pullback along a scheme map, so it supplies v^*K in the same site as the support prerequisite. No etale/pro-etale equivalence or preservation-of-injectives theorem is being inferred from a definition.

I opened the statement of every dependency, including the scheme-property collection: it explicitly says it fixes no notion of its own, and its list does not define etale morphisms. That is why the etale node is directly named. I also read the support convention `def-pur-flasque-support`, which fixes a closed immersion, its open complement, finite coefficients and the small pro-etale sites. All of those remain inherited from the triangle referenced in the item's opening words. No new boundedness or coefficient assumption was added.

C1/C4 check: there are no proof steps or cited theorem applications. `proof`, `proof_deps` and `proof_origin` remain empty/empty/null, and `citations.json` is empty. The statement dependencies supply notions, without borrowing conclusions from hidden proofs. In particular the current etale support construction is not used as a pro-etale theorem.

B1-B9 check: no unsplit child statement, Mathlib leaf, new notation convention or new node was created. The item retains the imported source/order, TeX, blueprint fields and import flags. Its own Mathlib searches were rerun through msearch.py with exact query text recorded in `mathlib_searches`; LeanSearch failed with HTTP Internal Server Error and is recorded as unavailable. Loogle returned generic triangle/morphism definitions; LeanFinder's two phrasings returned categorical-localization and resolution ingredients, not this whole definition. Mathlib `CategoryTheory/Triangulated/Basic.lean:44,104,137,146` was read for the generic triangle, three-square morphism, composition and triangle category. Nothing is being declared a leaf from a partial hit.

B10/duplicates: the project-source search found no exact attachment. Whole-DAG and whole-blueprint searches for support-localization and canonicality returned the construction, this definition and the theorem asserting its properties. The construction is not this meaning definition; the theorem refers to this definition rather than defining its notions. There is no distinct same-as blueprint node, so `blueprint.same_as=[]`. The imported item has `blueprint.is` equal to its own id and `from=null`; there is no unspecified created-node ancestry to fill. No new-node tag pairs exist.

D/E and small cases: there is no relabelled child lemma, circular proof, unstated theorem application or new mathematical assertion to test. The zero input is allowed, and a chosen resolution is not assumed to be literally the zero complex. For Z empty or Z=X the same definition compares the corresponding support triangles, with the closed/open pair and pullback domains still meaningful. The identity etale map gives the original pair; successive etale maps use the defined fibre products, without asserting extra coherence beyond the imported clauses. The comparison is of whole triangles, including the connecting map, not just of their three objects. No coefficient value is used to identify different categories.

## Validation

Only read-only source searches, Mathlib searches and stage-1 DAG checks were run. No Lean, compiler, Lake or build tool was run. Direct `tools/review_split.py` in the shared checkout raises a path error because its `head_version` tries to relativize the externally linked live DAG against the shared checkout root; this is an installation issue, not a bypass. The required delivery tool runs the maintainer's preflight against the materialized delivery tree instead.

The final dry-run result is recorded in `repair-dry-run.log` in this sandbox. No push is authorized at this worker stage; the accepted sandbox is for the next reader.


## Second reading by NO

Independent reading on 2026-10-16. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the worker contract and stage-1 rules, and the imported chapter and unit. This is a definition split under stage 1 §3(2), not a theorem split. There are zero proof steps and zero new nodes; consequently there are no per-step theorem citations or new-node B1–B7 obligations to discharge, and citations.json correctly remains [].

- Item, canonicality clause: checked against the archived blueprint `sec-smooth-purity/sk-prop-a1-kummer/def-pur-triangle-meaning.md`, order 1932, and the current `def-pur-support-triangle` and `def-pur-kinjective-complex`; PASS. It defines independence under derived comparison maps, rather than equality of chosen resolutions or an assertion that comparisons have already been proved.
- Item, functoriality clause: checked against the same blueprint clause, `def-weil-abstract-derived-category`, and its `def-weil-triangulated-category` dependency; PASS. The latter defines morphisms of triangles by all three commuting squares, including the square with the shifted first component. Composition is in the derived category, with no presumed strict functorial choice of resolutions.
- Item, etale base-change clause: checked against the same blueprint clause and the statements of `def-weil-etale-morphism`, `def-pc-base-change`, and `def-weil-proetale-inverse-image`; PASS. The domains are $Z\times_X X'$, $U\times_X X'$, and complexes on $X'_{\mathrm{proet}}$ with the original constant finite coefficient ring. The definition imposes compatibility of the whole triangle, not just of its objects, and does not prove preservation of injectives or a base-change isomorphism.
- Statement dependency `def-pur-support-triangle`: opened its full statement and its four statement dependencies; PASS. The chosen resolution has injective terms, the support is the kernel for the closed–open pair, and the cone differential is the one in the archived order-1931 construction. Its current ringed-site resolution dependencies cover pro-etale sheaves; the obsolete etale-only resolution interface is not used.
- Statement dependency `def-weil-scheme-morphism-properties`: opened its full statement; PASS as an inherited collection only. It explicitly defines no notion itself and does not supply etale morphisms, so the worker correctly names the etale definition separately.
- Statement dependency `def-weil-etale-morphism`: opened its statement and Stacks `morphisms.tex`, Tag 02GI / `definition-etale`, Tag 02GV / `lemma-flat-unramified-etale`, and Tag 02GE / `lemma-diagonal-unramified-morphism`; PASS. Locally finite presentation, flatness, and unramifiedness have the stated meaning, with no extra separatedness or quasi-compactness requirement.
- Statement dependency `def-pc-base-change`: opened its full statement; PASS for the fibre products and their projections. Its separate structure-sheaf-module clause is not being used for the constant-coefficient pro-etale module pullback.
- Statement dependency `def-weil-proetale-inverse-image`: opened its full statement and Stacks `proetale.tex`, Tag 09A5 / `section-morphism`; PASS. For $f:X\to Y$, the site functor is $Y_{\mathrm{proet}}\to X_{\mathrm{proet}}$, taking a test object over $Y$ to its base change over $X$; its inverse image and constant-ring extension of scalars supply the pullback used here. Applied degreewise this is the input complex notation; no theorem about injective replacements is inferred from it.
- Proof steps: checked `proof=[]`, `proof_deps=[]`, `proof_origin=null` against the definition-only blueprint body; PASS, no omitted proof is moved into a new node.
- New nodes: checked every sandbox node file against existing ids; none are new. No elementary lemma, duplicate, renamed clause, or Mathlib leaf was introduced.

Source availability correction: the two Wanted entries above accurately describe the shared checkout, where those files are absent, but a second-reader filesystem search located the complete archive at `/home/ubuntu/work-bp/sheaf/literature/blueprint/`. Its COMMITS.txt records master `967897d1c5e775be739997d7e847a9205fae1359`, exactly SETUP.md's import source. I opened both requested files there and compared the item's statement to the order-1932 body programmatically: exact equality. I also opened the neighboring order-1933 theorem to confirm that it asserts the properties defined here and is not another definition or a dependency to add. No source remains wanted for this item. Stacks sources above were read from `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`, using `tags/tags` to resolve the tag-label pairs; none was installed or written to the shared repository.

Duplicate and attachment checks: searched all 2,943 archived blueprint Markdown files for support-localization with canonicality/functoriality, plus whole-DAG blueprint searches for `support-localization`, `canonicality`, `resolution`, and `base-change compatibility`. Only this meaning definition and the neighboring construction/property theorem concern these three conditions. I read the etale source `SixFunctors/OpenClosed/Supports.lean:157,169` and `Etale/Derived/LocalizationBaseChange.lean:78`: they respectively construct an etale triangle and prove boundary compatibility for a different etale interface, and do not define the three pro-etale conditions. The node-id/name-map search gives no exact attachment. No master sorry declaration was counted as a proof.

Independent Mathlib searches: ran msearch.py with the new LeanFinder phrasing recorded in the node, the categorical grep pattern `support.*triangle|triangle.*support|locali[sz]ation.*triangle`, and Loogle `"TriangleMorphism"`. LeanFinder returned eight derived t-structure hits; grep returned zero hits; Loogle returned generic triangle maps and composition. I read Mathlib `CategoryTheory/Triangulated/Basic.lean:44,104,124,137,146` to check their scope. These provide ordinary triangle language, already reachable through the existing derived-category dependency, and do not make this sheaf-specific definition a Mathlib leaf. All three actual queries and results are in searches.jsonl and mathlib_searches; the first worker's recorded searches are retained.

Edge cases: $K=0$ does not force the chosen resolution to be literally zero; comparisons take place in the derived category. For $X=\operatorname{Spec}k$, the two closed subsets are $Z=\varnothing$ and $Z=X$, and both closed–open pairs still give meaningful compatibility conditions. For $X=\varnothing$ the pullback domains and zero sheaf category remain meaningful. The identity etale arrow gives the original pair, and an empty etale source gives the empty base-changed pair. The inherited finite coefficient convention allows $n=1$ and requires $n\geq1$; this item introduces no $n=0$ case or additional bound. No mathematical assertion was discovered to be false or ill-typed, and no statement dispute or change is needed.

Changes made in this second reading:

- Added three independently executed Mathlib search records to the existing item, retaining the original records and statement.
- Resolved the report's source-availability limitation by locating, opening, and comparing the pinned local blueprint archive; the earlier worker sections remain intact.
- Added this clause-by-clause and dependency-by-dependency second reading. No node statement, dependency, proof, citation, Lean file, chapter, or unit was changed.

Validation: only source reads, logged searches, JSON inspection and the prescribed stage-1 delivery tool are used. No Lean, compiler, Lake, build, or direct git command is run. The dry run and delivery below materialize the current upstream baseline in the delivery tool's temporary worktree.
