## Files written

- dag/nodes/sec-smooth-base-change/sbc-lem-etale-locality.json: statement split into six steps; no full Mathlib match.
- citations.json: one verbatim statement quotation for every node cited in every step.
- report.md: this worker's report. Sandbox preparation scripts are not delivery files.

No new nodes and no new Mathlib leaves. An earlier sandbox draft existed when this worker started; I independently read its sources and citations, expanded the inverse-image/restriction identification, refreshed searches, and replaced its report. This is the first-worker handoff; a fresh second reader still must read and deliver it.

## Attachments

No full attachment. Read WeilConjectures/SixFunctors/Etale/SmoothBaseChange/Locality.lean:368–493 in slopmaster2. AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_etale_cover (475), AlgebraicGeometry.Etale.isIso_baseChange_app_of_etale_cover (423), and AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale_cover (439) have sorry-free displayed proofs, but their sheaves are ModuleCat over a commutative ring and their derived objects are DerivedCategory.Plus. They do not give the set-valued clause or the arbitrary unbounded derived clause. No upstream master sorry is counted as finished.

## WANTED

None: the relevant Stacks sources are local.

## Faults corrected

The imported proof cited the etale-site definition for localization and isomorphism detection, although that definition states neither theorem. It also wrote F restricted to V_i when F is on T; the correct restriction is to T_i=V_i times_S T. The replacement uses theorem statements and distinguishes these two sites.

The bounded-below exchange lemma is insufficient for arbitrary K. I retained unbounded K-injective computations, rather than silently restricting the statement. The abelian underived-exchange and cover detector are not applied to sets. Set-valued localization uses the general slice-site statement and descent is written by sheaf equalizers.

The equality notation in the statement is the source's shorthand for invertibility of the canonical base-change map: Stacks 0EZR's proof explicitly interprets it that way. No mathematical hypothesis or conclusion changed. Removed the unstable bibliographic number 59.86.1 from the final parenthesis; Tag 0EZR remains. The diagram and all three clauses agree with the source.

## What remains

Nothing unresolved in this one-level split. Existing dependency nodes keep their own states. No delivery or push is requested here; a second worker takes over after the accepted dry run.

## Not duplicates

No new nodes. I searched the entire DAG for 03EF, 0D6G and 0EZR, and searched titles/statements for localization, restriction, direct image and K-injectives. Blueprint searches for “etale locality”, “restrict-direct-image-open”, “localize-morphism-strong”, and “restriction” found no other blueprint statement giving this entire item. The other locality blueprint concerns cohomological smoothness, not base-change maps. Existing general slice-site and K-injective results suffice, so no new 0D6G node is needed.

## Mathlib searches

The item's recorded searches are the exact msearch.py queries rerun by this worker. LeanFinder's etale phrasing returned Kahler base change, sheaf pullback construction, underived pushforward and etale composition. The unbounded-localization phrasing returned exact-functor derived factorization and rightDerived_map_eq, not slice-site localization of total direct images. Loogle returned sheafification and localization-class isomorphism criteria. The grep returned geometric precoverage base-change stability and Zariski ring localization. None covers this three-clause item. I also read Mathlib/CategoryTheory/Sites/Continuous.lean:360–402 and Over.lean:510–534: these give underived composition and slice restriction identities, not the unbounded exchange theorem. LeanSearch returned Internal Server Error; recorded as unavailable. There are no new nodes requiring their own searches.

## Review by NO

I read Stacks etale-cohomology.tex, Tag 0EZR, label lemma-base-change-local, its full statement and proof, and the imported blueprint text. I read Sites 03EF, label lemma-localize-morphism-strong, and sites-cohomology.tex 0D6G, label lemma-restrict-direct-image-open, 08FI, label lemma-restrict-K-injective-to-open, and remark-base-change. The source expressly allows K in the unbounded D(T_et). The chapter and sk-def-bc unit record the localization route and no proof steps requiring a different reduction here. Neither unit nor chapter is edited.

Step 1: I opened each cited statement. Etale-base-change-finite-limits gives etale projections and finite limits; etale-base-change-continuous gives cover preservation and direct image on sets; sets-etale-inverse-image-exact makes these functors morphisms of sites. Site-localization-open applies to every etale object despite its name, and identifies coverings. The localized-site definition gives sectionwise restriction. Slice-site-localization gives both functor comparisons. Site-morphism-composition supplies the adjunction-compatible comparisons on sets and groups. I added the sets-adjoint-continuous-restriction-adjunction citation and its application: composition of etale objects is left adjoint to fibre-product base change by the fibre-product mapping property. Both precompositions preserve sheaves by covering compatibility, so the cited statement identifies scheme inverse image with restriction and identifies its unit. This closes an implicit identification in the earlier draft. For g the objects are V_i and T_i; for h they are U_i and Y_i. Fibre-product associativity gives Y_i=U_i times_{V_i} T_i. All sites and slices use a common sufficiently large universe.

Step 2: prop-pur-kinjective-resolutions-exist supplies arbitrary resolutions on small ringed sites, and lem-pur-kinjective-restrict-localized supplies restriction of K-injectives with no boundedness hypothesis. With constant Z, modules are abelian sheaves. The total-derived lemma requires a triangulated functor on the homotopy category: direct image is additive, hence preserves the finite biproducts and differential matrices of shifts and cones. Its composite with Q therefore meets that hypothesis. The displayed representative calculation is exactly the proof of 0D6G. Site-restriction-exact and exact-functor-derived-factorization justify termwise derived restriction; inverse-image-exact justifies termwise f and e inverse images. These are statements, not details borrowed from dependency proofs.

Step 3: I checked the arrows, not just their endpoints. The direct-image comparison is the identity on fibre-product sections. Its inverse-image comparison is the adjunction-compatible one, so the counit corresponds to the identity under the local adjunction. The step displays its restricted transpose. For the derived version, I checked K-injective existence, the K-injective definition, and the Hom-to-K-injective derived bijection. Exact inverse image implies direct image preserves K-injectives by termwise adjunction, including homotopies. Thus the derived adjunction into those targets is the termwise one. The explicit chain map with a resolution e^{-1}I to J computes the canonical counit-transpose exchange defined in sbc-def-base-change-map. Restricted I and J are K-injective and the restricted resolution is a quasi-isomorphism by exact restriction. This proves compatibility of the actual arrows. The unit-composite and counit-transpose formulas agree by naturality and triangle cancellation, as written in the step; no assumption that e inverse image preserves K-injectives occurs.

Step 4: the only citations are the cover-preservation statement and the equalizer definition of a set-valued sheaf. Local inverses agree on overlaps by injectivity, glue uniquely, and commute with restriction by uniqueness. This is a direct elementary argument from those statements; no separate set-descent theorem is hidden.

Step 5: exact restriction preserves the kernels, images and quotients defining cohomology, as stated in the abstract-derived-category definition. The cover detector explicitly concerns abelian sheaf maps and is applied to each H^r. The unbounded-derived-iso-cohomology statement detects isomorphisms from all integer degrees. No bounded-plus theorem is substituted.

Step 6: sbc-def-base-change-map and direct-image explicitly give the degree-q convention H^q of exchange and R^q=H^qR. F in degree zero is bounded below, so that convention applies. Restriction compatibility follows from steps 2–3 and exactness as in step 5. The abelian cover detector uses only the degree-q hypothesis, not invertibility in every degree.

I tested singleton identity covers, identity squares, empty schemes with empty coverings, zero sheaves and complexes, negative degrees, and complexes unbounded below. Empty sheaf equalizers force singleton sets; abelian sheaves are then zero. Every cohomological argument is degreewise without truncation. No finite-type, properness, qcqs, or coefficient-torsion assumption was introduced. There are no new statements to test under B1–B9 or D1–D2. C1–C4 are checked by the opened statements and the explicit elementary calculations; citations.json copies those statements verbatim. General off-unit theorems are declared in split_report.tool_uses with their precise use because sk-def-bc contains no such tool statements. I checked dependency traversal for cycles and retained imported metadata. No live project, launcher, Lean source, or compiler is modified or invoked by my work.

Broader dependency audit: the existing closure contains the baseline cycle lem-weil-pbc-sheaf-algebraic-structures-abelian-component → lem-weil-pbc-sheaf-algebraic-structures-objects → lem-weil-pbc-sheaf-algebraic-structures-abelian-component, reached through sbc-def-base-change-map. Both edges are already in repository nodes outside this worker's scope. I report it rather than editing those nodes. The item adds no cycle: no existing statement/proof dependency of any cited node reaches sbc-lem-etale-locality. The authorized delivery preflight passed; it does not reject this inherited baseline defect.

## Second reading by NO

Item statement: compared each scheme, factorization, Cartesian square, restriction, and all three clauses with etale-cohomology.tex Tag 0EZR, label lemma-base-change-local (16307–16373); PASS. Equality means the canonical map is invertible, as the source proof expressly says. No change of mathematical statement or hypotheses is required.

Step 1: opened all eight cited nodes; compared the slice direct/inverse-image identities with sites.tex Tag 03EF, label lemma-localize-morphism-strong. PASS: continuity, finite limits, and the exact set inverse image apply to arbitrary scheme morphisms; the slice equivalence applies to arbitrary etale objects. The elementary lambda/base-change adjunction supplies the scheme restriction identification, including its unit.
Step 2: opened the six cited statements and sites-cohomology.tex Tag 0D6G, label lemma-restrict-direct-image-open, and Tag 08FI, label lemma-restrict-K-injective-to-open. PASS after spelling out additivity sectionwise. Constant Z modules are abelian sheaves; small sites admit the cited unbounded resolutions, restriction preserves K-injectives, and additive direct image preserves the displayed cone matrices. There is no boundedness or injectivity-preservation assumption on inverse image.
Step 3: opened every cited statement, especially sbc-def-base-change-map's inverse-image transpose formula and lem-weil-pbc-kinjective-hom-derived's Hom bijection. PASS: the counits are identified through the adjunction-compatible localization comparisons; the displayed chain map has target h_*J, not h_*e^{-1}I assumed K-injective. Exact inverse image sends acyclic complexes to acyclic complexes, so the written Hom/homotopy argument proves preservation of K-injectives by direct image and validates the derived counit computation. The restricted resolution remains a quasi-isomorphism into a K-injective complex.
Step 4: opened etale-base-change-continuous and the set-sheaf equalizer definition, and compared with the final sentence of 0EZR's proof of (1). PASS: the inverse sections agree on overlaps by local injectivity and glue uniquely; naturality follows by uniqueness. This is elementary and uses no abelian cover detector for sets.
Step 5: opened site-restriction-exact, abstract-derived-category, etale-cover-detects-iso, and unbounded-derived-iso-cohomology. PASS: exact restriction preserves the kernel/image/quotient cohomology formula, the cover theorem is applied only to abelian sheaf maps, and detection ranges over all integer degrees, including complexes unbounded below.
Step 6: opened base-change-map's degree-q convention, direct-image's higher-image definition, and the abelian cover detector. PASS: only the specified degree-q hypothesis is used; removed the unnecessary uncited negative-degree vanishing assertion.
New nodes: none; B1–B9 and duplicate/special-case pruning have no new statements to examine. Existing generic tools are strictly smaller than the item; no clause is transferred into a new node. The six steps prove the item rather than citing its restatement.

Small cases: identity square and singleton identity cover give the original map; zero abelian sheaves and complexes give zero maps; on empty schemes the empty sheaf equalizer gives singleton sets and zero abelian groups, so empty covers are allowed. Over a field no additional finiteness condition is needed. Degrees 0, 1, and negative degrees are handled by the same cohomology comparison, without truncating unbounded K. No statement dispute found.

Independent searches: ran msearch.py with LeanFinder query “Restriction to slice sites commutes with derived pushforward and detects isomorphisms” (eight hits: underived sheaf pushforward comparisons and open module restriction composition, no full match); grep “isIso.*baseChange.*cover|baseChange.*of_etale_cover” (zero Mathlib hits). Loogle query “CategoryTheory.Sheaf, CategoryTheory.Functor.IsConservative” returned an unknown-identifier diagnostic, not evidence of absence; reran valid “CategoryTheory.Sheaf, CategoryTheory.IsIso” (twelve sheafification/localization hits, no full match). Actual output is preserved in searches.jsonl. Read slopmaster2 Locality.lean:368–493: the recorded cover results concern ModuleCat and DerivedCategory.Plus, so neither the set-valued clause nor the unbounded clause is finished by those declarations.

Changes: expanded step 2's elementary additivity calculation; removed step 6's unnecessary vanishing claim; removed split_report.tool_uses because delivery-errors C8 reserves approval of off-unit tools to the maintainer. The proposed tools and their reasons are listed below for that reviewer. First-worker sections, including Review by NO, remain unchanged; its claim that it recorded tool_uses describes the pre-second-reading draft. Citations retain verbatim quotations from the opened nodes; their citation sets did not change. The extra trailing dot in the supplied delivery command is rejected by the script's two-positional-argument parser, so the dry run and delivery use the documented syntax without it.

Off-unit tool requests (maintainer to record; no approval asserted here):

- lem-weil-pbc-etale-base-change-finite-limits: Supplies etale stability and finite-limit compatibility of base-change site functors. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-etale-base-change-continuous: Supplies preservation of coverings and the direct image on set-valued sheaves. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-etale-site-localization-open: Identifies a small etale slice at an arbitrary etale object with that object's etale site. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-slice-site-localization: General localization comparisons for inverse and direct image, including sets; the unit has no such theorem. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-site-morphism-composition: General adjunction-compatible composition on sets and abelian sheaves. Used as a general tool; sk-def-bc has no statement supplying it.

- prop-pur-kinjective-resolutions-exist: Unbounded K-injective resolutions on small ringed sites; needed because the source allows arbitrary K. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-pur-kinjective-restrict-localized: Unbounded restriction of K-injectives; replaces the insufficient bounded-below etale exchange lemma. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-kinjective-total-derived: K-injective representatives compute total right derived functors. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-site-restriction-exact: Exactness of restriction on arbitrary slice sites. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-exact-functor-derived-factorization: Termwise realization of exact restriction on unbounded derived categories. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-etale-cover-detects-iso: Generic abelian sheaf descent for isomorphisms on an etale cover. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-unbounded-derived-iso-cohomology: Unbounded derived isomorphisms are detected by all cohomology functors. Used as a general tool; sk-def-bc has no statement supplying it.

- lem-weil-pbc-sets-etale-inverse-image-exact: The exact inverse image of sets makes the scheme base-change functor a morphism of sites, as required by the slice-localization theorem. General tool absent from sk-def-bc.

- prop-weil-pbc-inverse-image-exact: Exactness of abelian inverse image permits its termwise action on the unbounded derived category. General tool absent from sk-def-bc.

- lem-weil-pbc-kinjective-hom-derived: identifies Hom into K-injectives in homotopy and derived categories, giving the derived adjunction comparison directly.

- lem-weil-pbc-sets-adjoint-continuous-restriction-adjunction: Identifies the scheme inverse image along an etale object with restriction, with its unit, on sets. Generic adjunction tool absent from sk-def-bc.
