# Stage-1 report: def-weil-constructible-standard-tstructure

## Files written

- `dag/nodes/sec-smooth-purity/def-weil-constructible-standard-tstructure.json`: existing definition, status `split`, ten existing statement dependencies; refreshed actual Mathlib search records and split report. The on-disk directory is retained; the maintainer-owned chapter/unit remain `sec-smooth-base-change` / `sk-rem-rest`.
- `citations.json`: `[]`, since the definition has no proof steps.
- `report.md`: current worker review, replacing stale stage-2 blocker reports.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, `(blueprint: def-weil-constructible-standard-tstructure)`, standard-pair and constructible/t-structure names found no exact declaration. Read `CategoryTheory/DerivedCategory/Constructible.lean` and `SixFunctors/ProEtale/Derived/Constructible.lean`: the former defines bounded constructible étale complexes; the latter defines complexes of étale origin and explicitly warns at lines 47-51 that this is wrong for integral ell-adic coefficients. Neither states the integral, rational and common-stage pair in this item. Exact upstream master was read only as reference material; its nearby bounded-constructible definition gives no attachment for these three categories.

## WANTED

None. The archived blueprint, Stacks source and Bhatt–Scholze paper are available read-only under `/home/ubuntu/weil-launcher-nt/literature/`. The paper text in this sandbox was opened at 6.8.8–6.8.14.

## Corrections and scope

The base node is a definition, so stage-1 §3(2) requires its constituent notions rather than a theorem proof. The earlier mathematical split already made the uniformizer and integral object domain explicit, cited cohomological shifts and bounded t-structures directly, and located the actual ancestor sentence. I retained those repairs. There are zero new nodes, zero Mathlib leaves, and no proof obligations moved into a clause-shaped child. `proof = []`, `proof_deps = []`, and `proof_origin = null` are appropriate here.

The earlier BLOCKED entries referred to a stage-2 return at f6a5db2296f7 and to restrictions on the delivery tool's temporary worktree. The current `coord/returns/NG.md` has no return for this item, and this dispatch explicitly authorizes `deliver.py --no-push`. Accordingly this attempt completes the stage-1 task. It claims no Lean implementation, compilation or stage-2 repair. No agents were started and nothing was pushed.

No mathematical statement dispute was found. One precision issue in the inherited source metadata is reported: Bhatt–Scholze 6.8.14(2) gives an equivalence, not literal equality, and the constructible-sheaf discussion assumes X topologically noetherian. The definition itself asserts neither that equivalence nor the t-structure theorem for arbitrary schemes. Its predicates make sense for any scheme Y; the final sentence identifies the separate bounded-t-structure assertion for finite-type k-schemes. The maintainer-owned source field was retained.

## Blueprint and duplicate search

Read `dag/chapters/sec-smooth-base-change.json`, `dag/units/sk-rem-rest.json` and their archived `_section.md` sources. The unit's last clause explicitly includes pro-étale, adic, rational and algebraically closed coefficients; it has no proof steps to realize. This item is not the unit's key statement, so its realization record is unchanged.

`tools/blueprint_refs.py ancestor def-weil-constructible-standard-tstructure` returns `def-weil-constructible-heart`. Opened that archived node: the sentence beginning “For every $m\in\mathbf Z$, write” and its following displays are exactly the ancestor place made precise here. The item does not assume existence of those truncation functors in order to define its predicates.

Whole-blueprint searches for `standard` and `t-structure`, and whole-DAG searches for standard pairs, cohomology-vanishing subcategories and rational isomorphism closures found no duplicate of this three-level definition. Read the nearby `def-sbc-standard-tstructure-derived-category`, `def-weil-pbc-bounded-derived-subcategories`, `prop-constructible-truncations`, `prop-weil-pbc-integral-tstructure` and `prop-weil-localized-tstructure`: these concern ambient categories, boundedness or theorem assertions, rather than this three-level pair on the detailed coefficient constructions. `blueprint.same_as = []` is retained. No new node needs a “Not duplicates” pair list.

## Mathlib searches

Fresh searches used only the required `msearch.py NG def-weil-constructible-standard-tstructure` command, recorded verbatim in the item's `mathlib_searches` and its appended `searches.jsonl`. Both semantic phrasings, both Loogle patterns, the homological-algebra grep and the algebraic-geometry grep were read. LeanSearch returned Internal Server Error and is recorded as unavailable.

Read the hit sources: `DerivedCategory/TStructure.lean` lines 34-121 defines the ambient canonical t-structure and the cohomology-vanishing characterizations; `Triangulated/TStructure/Induced.lean` lines 35-100 requires a triangulated subcategory and a truncation-triangle condition. These cannot be one-line matches for all the integral, scalar-localized rational and finite-stage categories of this item. Abstract triangulated localization hits likewise do not define these classes. No Mathlib match is claimed. Historical records are retained, including the earlier invalid `Mathlib/Mathlib` path explicitly marked invalid; the present conclusion uses correctly rooted fresh searches.

## Review by NG

I performed this worker self-review with the node statements and sources open; this is not a claim that I am the independent second reader.

For the item, I read the two integral cohomology-vanishing displays of archived `prop-weil-pbc-integral-tstructure.md`, the two isomorphism-closure displays of `prop-weil-localized-tstructure.md`, and the actual `def-weil-constructible-heart.md` sentence/displays. These supply the intended classes, while the concrete coefficient categories come from the following existing definitions. I did not import the neighboring propositions' levelwise-truncation claims into this definition. Bhatt–Scholze 6.8.11(3), under its topologically noetherian hypothesis, characterizes constructible integral objects by bounded constructible cohomology. Definition 6.8.8 and Proposition 6.8.14(1)-(2) explain the rational and finite-coefficient motivation. Stacks `homology.tex`, Tag 0118, label `section-truncations`, and `derived.tex`, Tag 08J5, label `remark-truncation-distinguished-triangle`, were checked for the ambient cochain convention; they do not supply rational or common-stage t-structure axioms.

- Coefficient data: opened `def-weil-finite-field-fiber`, `def-weil-l-adic-numbers`, `def-weil-algebraic-closure` and `def-weil-l-adic-coefficient-extension`. They supply prime p, a >= 1, q = p^a, the chosen finite field and its closure, prime ell unequal to p, Q_ell, its algebraic closure, finite E/Q_ell, its valuation ring and chosen uniformizer. Every coefficient hypothesis used in the statement is present. The rational E need not itself be a subfield of the fixed algebraic closure; the common-stage clause separately restricts its fields to that closure.
- Integral clause: opened `def-weil-derived-complete-integral-detailed` and `def-weil-completed-integral-coefficients`. The former is a full subcategory with derived completeness, constructible finite reductions and a uniform reduction amplitude. The latter defines the completed coefficient sheaf as the inverse limit of the finite constant coefficient sheaves, its module category, and its ambient derived cohomology. Thus H^r(K) is not cohomology over the discrete constant O_E sheaf and not the cohomology of a levelwise tower. The two inequalities define full classes inside precisely that category.
- Rational clause: opened `def-weil-rationalization-karoubi`. It explicitly says “same objects”, localizes Hom groups by tensoring with E and takes no Karoubi completion. Consequently the existential representative L lies in the integral class but its isomorphism to K is in the rational category, exactly as written. No claim that all integral representatives have the same integral amplitude is used.
- Algebraically closed clause: opened `def-weil-algebraically-closed-coefficients`. It defines pairs (E,K), common-extension Hom colimits and shifts (E,K)[1] = (E,K[1]). Existence of an isomorphism to some finite-stage (L,M) defines the two classes without assuming scalar-extension t-exactness or independence of a selected representative. This is a predicate on its actual pair category, with no idempotents adjoined.
- Shifted classes: opened `def-weil-abstract-derived-category`, which gives (K[1])^r = K^{r+1}. Therefore H^r(K[n]) = H^{r+n}(K); the condition K[n] in the nonpositive class is vanishing above n, and the nonnegative condition is vanishing below n. The plus sign is correct. Opened `def-weil-t-structure` to verify that the phrase bounded t-structure in the final sentence refers to a separate axiom/property package, not an assertion proved by this definition.

There are no proof steps or proof citations to audit for C1/C4, hence no citation quotes to fabricate. All ten statement-dependency files were checked for the exact notions taken above, and all referenced ids exist. B1–B9 are satisfied with no newly created nodes; source locations and single-escaped TeX were checked. C3–C8 and D1–D5 introduce no hidden proof, cycle-producing theorem citation or change of unit route. The split retains only definition dependencies; it does not cite the heart ancestor as a mathematical dependency.

For E1–E6 I tested zero, the empty scheme and shifted degree-zero modules. Zero satisfies both inequalities and both existential isomorphism predicates. On the empty scheme all objects are zero. For Y = Spec(k), a degree-zero finite free coefficient module is in both classes; its [1] shift lies in degree -1 and its [-1] shift in degree 1, confirming the n-index signs at n = 0 and 1. A degree-zero module O_E/varpi_E and any shift become zero after rationalization because varpi_E annihilates its identity; the rational isomorphism closures correctly contain these objects in both classes. This checks why rational membership must use rational isomorphisms, rather than integral cohomology of the same raw object. No extra noetherian or finite-type hypothesis is needed merely to define these predicates, and no t-exactness or boundedness theorem has been silently used.

## Unfinished work

None within this stage-1 item. A fresh second reader must review and deliver the accepted sandbox, as the brief requires. The current worker performs only the no-push dry run.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NG def-weil-constructible-standard-tstructure --no-push` printed `OK (not pushed)` and `preflight passed` at dry-run head `16c26f7a0c`. The final sandbox, including this validation note and the corrected search-result count, is checked once more with the same command before READY. No compiler or Lake/build tool was run. Nothing was pushed; the accepted sandbox is reserved for the independent second reader.


## Concurrent DAG preflight finding

The final repeat failed solely in the global DAG comparison, reporting unrelated
missing nodes and step/proof-dependency mismatches. Examples were
`lem-sc-valuation-closed-fibre-divisibility` step 3,
`new-module-cup-derived-homology-tensor` referencing missing
`def-sc-module-cup-derived-class-comparison-data`,
`def-weil-pbc-strict-henselization-limit` steps 1-3, and the square-zero section
nodes referencing missing `def-pc-quasi-coherent-sheaf`. None names this item
or any of its ten statement dependencies. The delivery changed no such node.

Read `tools/preflight_delivery.py:519`, `tools/dag_delta.py`,
`dag_queue.nodes_dir()` and the current delivery wrapper. Preflight compares
candidate and archived-base findings. The current wrapper explicitly sets
`SHEAF_DAG` to its temporary candidate node directory, so the worker's
absolute live-mirror setting is not sufficient to explain this failure.
The exact cause of the inconsistent first-pass/second-pass global findings
is not established. The item-specific review passed (no failure was
reported for `review_split.py`). The unrelated findings cannot be repaired
by changing this mathematical split. This worker has not edited tools,
coordinator files or unrelated nodes, nor overridden their environment.
A fresh ordinary no-push dry run
is attempted after this note. READY is returned only if that final run prints
OK; otherwise the reported result is BLOCKED on this exact tool failure,
despite the earlier passing run. No delivery is made in either case.


## Second reading by NG

I am the independent second reader of this dispatch. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the worker contract and stage-1 definition rule, the item, all ten dependency statements, and the cited source passages. The work remains stage 1, with no Lean writes, compiler/build calls, delegation or changes to the shared repository.

- Item, integral clause: checked the two displays in archived `prop-weil-pbc-integral-tstructure.md` and Bhatt–Scholze Proposition 6.8.11(3), together with the actual completed-integral coefficient definition; PASS, the cohomology is that of completed-sheaf modules.
- Item, rational clause: checked both isomorphism-closure displays in archived `prop-weil-localized-tstructure.md` against the same-object Hom localization in `def-weil-rationalization-karoubi`; PASS, the existential isomorphism is in the rational category.
- Item, algebraically closed clause: checked the pair objects, common-extension Hom colimit and shift in `def-weil-algebraically-closed-coefficients`, with Bhatt–Scholze 6.8.14(1)–(2) as motivation; PASS, membership is an existential finite-stage image closed under isomorphism, with no unproved assertion that every representative has the same amplitude.
- Item, shifted classes and final sentence: checked the cochain convention in `def-weil-abstract-derived-category`, the bounds in `def-weil-t-structure`, Stacks 0118 (`homology.tex`, `section-truncations`) and 08J5 (`derived.tex`, `remark-truncation-distinguished-triangle`); PASS, H^r(K[n]) = H^{r+n}(K), so the plus sign is correct; the bounded-t-structure theorem is expressly separate.
- Proof steps: none (`proof = []`); PASS under stage-1 §3(2), since the item defines predicates, not a theorem. The empty `proof_deps`, null `proof_origin` and `citations.json = []` are exact; there are no uncited proof facts or citation quotes to add.
- New nodes: none; PASS, no elementary fact, duplicate, clause-shaped restatement or Mathlib declaration was unnecessarily introduced.
- Dependency `def-weil-finite-field-fiber`: checked its tuple and ell-not-p coefficient convention; PASS, no geometric-base-change condition from its later paragraphs is imposed on the arbitrary Y here.
- Dependency `def-weil-l-adic-numbers`: checked Q_ell and its valuation ring; PASS.
- Dependency `def-weil-algebraic-closure`: checked the chosen field embedding and algebraic closure; PASS.
- Dependency `def-weil-l-adic-coefficient-extension`: checked finite dimensionality, valuation ring and chosen uniformizer; PASS.
- Dependency `def-weil-derived-complete-integral-detailed`: checked derived completeness, all finite reductions and their uniform amplitude; PASS, the item takes precisely this full-subcategory object domain.
- Dependency `def-weil-completed-integral-coefficients`: checked the inverse-limit ring sheaf, its module category and cohomology; PASS, no discrete constant integral sheaf is substituted.
- Dependency `def-weil-rationalization-karoubi`: checked same objects, Hom tensor E, induced shifts and absence of an added Karoubi envelope; PASS.
- Dependency `def-weil-algebraically-closed-coefficients`: checked finite subfields of the fixed closure and pair objects (E,K); PASS.
- Dependency `def-weil-abstract-derived-category`: checked H^r as a functor and cochain shifts; PASS.
- Dependency `def-weil-t-structure`: checked strictly full classes and boundedness terminology; PASS, it is used for terminology rather than to assert an unproved property of these classes.
- Duplicate/blueprint audit: reran `blueprint_refs.py ancestor` and whole-blueprint `search 't-structure'`, read the archived heart ancestor, chapter/unit records and nearby ambient/bounded/truncation nodes; PASS, none duplicates the integral/rational/common-stage predicate definition. The exact ancestor sentence is recorded; no theorem node is cited back to create a cycle.
- Mathlib/project audit: independently ran `msearch.py` LeanFinder with “cohomology vanishing predicates on derived categories of modules and stability under isomorphism” and grep for `isLE_iff|isGE_iff` in `Algebra/Homology/DerivedCategory`; read the actual ambient declarations at `TStructure.lean:83–121`; PASS, these are only the ambient integral support predicates, not the full definition. Read both project Constructible.lean interfaces and searched by id and names in slopmaster2/master; no exact closed attachment. Master is reference material only.
- Edge cases: zero and the empty scheme satisfy both classes; for a degree-zero finite free module on Spec(k), its [1] shift is in degree -1, and the [-1] shift in degree 1, confirming n = 0 and 1. A degree-zero O_E/varpi_E and every shift become zero rationally since varpi_E kills their identities, so all belong to both rational classes; PASS. Isomorphism closure is elementary: integral isomorphisms give isomorphisms on every H^r; rational/common-stage witnesses are composed with the given isomorphism; shifts preserve isomorphisms. No t-exactness theorem is needed for these observations.

Changes made in this second reading:

- Appended two actual independent search records and this per-clause/per-dependency audit; updated the split summary to identify the independent check. Kept the first worker's `## Review by NG` and all original sections.
- Made the inherited source-metadata issue actionable for the maintainer: replace the description “D_cons(X_proet,O_E)[l^-1] = D_cons(X_proet,E)” by “the natural functor is an equivalence of triangulated categories, for topologically noetherian X” (Bhatt–Scholze 6.8.14(2), with the assumption preceding 6.8.6). Likewise qualify the contextual use of 6.8.11(3). The source field is maintainer-owned (`tools/node_fields.py`), so I retain it and supply the exact repair here. This is a source-description correction, not a false mathematical predicate or a statement dispute: the item asserts neither identification nor the t-structure theorem for arbitrary Y.
- Added explicit isomorphism-closure and rational torsion checks above to make the elementary observations reviewable. No mathematical statement or dependency needed repair; zero new nodes and zero Mathlib leaves.

The earlier concurrent preflight finding is historical. The required fresh dry run and delivery below determine this dispatch's outcome.

Second-reader validation: the fresh required `deliver.py NG def-weil-constructible-standard-tstructure --no-push` completed with `OK (not pushed)` and `preflight passed` at `61e1a9d1a4`. Its complete terminal output is retained locally as `second-reading-dry-run.log`. This supersedes the historical concurrent-DAG blocker above. The required push is now performed by the same delivery wrapper; no compiler or Lake/build command was run.
