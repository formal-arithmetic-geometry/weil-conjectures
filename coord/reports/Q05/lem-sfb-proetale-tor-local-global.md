# Worker report: lem-sfb-proetale-tor-local-global

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proetale-tor-local-global.json`: statement, split; no Mathlib match. Its statement and statement dependencies are preserved. Six proof steps establish both implications.
- `citations.json`: one verbatim statement excerpt for each node used in each proof step.
- `report.md`: this report. `searches.jsonl` contains the searches actually executed by msearch.py.

No new nodes, no new definitions, and no Mathlib leaves. This is not the key statement of its unit; no unit file is changed.

## Attachments

None. I searched the entire project `WeilConjectures/` for the blueprint id and Tor-amplitude terminology, then inspected `CategoryTheory/DerivedCategory/TorAmplitude.lean:59-111` and `SixFunctors/ProEtale/Derived/FlatModel.lean:46-77`. The first defines finite Tor amplitude and its interval operations; the second is a bounded-constructible flat-model equivalence. Neither gives the equivalence with locally finite Tor dimension for arbitrary complexes and arbitrary slice modules. No source declaration states this item exactly. The master checkout is not used as evidence of a finished proof.

## WANTED

None. All required sources are in the repository.

## Findings and changes

The imported node had no proof. Its statement is correct, including its absence of Noetherianity, quasi-separatedness, boundedness, constructibility, completeness, or coefficient finiteness assumptions. There is no STATEMENT-DISPUTED and no statement correction.

I read Stacks `proetale.tex`, Tag 09C2 (`lemma-describe-constructible-complexes`, lines 5788-5830), especially the sentence making the Tor interval uniform; Tag 09C1 (`definition-Dbc`) only provides the motivating adic setting. I read `sites-cohomology.tex`, Tag 08FZ (`definition-tor-amplitude`, lines 12377 onward) for the exact local definition, Tag 08H5 (`lemma-tor-amplitude-pullback`, lines 12543 onward), and Tag 07A4 (`lemma-pullback-tensor-product`, lines 3683-3724). I also read `sites-modules.tex`, the localization section and Tag 04IX (`definition-localize-ringed-site`, lines 1992-2048), and the exactness discussion; and `proetale.tex`, Tags 0989 (`definition-fpqc-covering`), 098B (`lemma-etale-proetale`), and 098C (`lemma-proetale`), around lines 2127-2215. The proof is marked agent-written because it spells out the uniformity argument that 09C2 compresses into one sentence.

The finite-refinement lemma already in the DAG, `lem-sfb-finite-affine-proetale-refinement`, assumes a Noetherian quasi-separated scheme. It cannot be used for the present statement. I instead apply condition (2) separately to a finite affine open covering of X. On each affine target, `sk-def-pe-site` explicitly supplies finite affine refinement. The site's composition axiom then supplies a finite covering of X. Thus the argument never infers that an arbitrary jointly surjective weakly etale family is a covering and never assumes the images of weakly etale maps are open.

The forward implication uses the existing general slice Tor restriction theorem. Restricting the tests of the global definition alone would be insufficient, since arbitrary slice modules need not be restrictions of global modules. The reverse implication only needs restrictions of global tests; their derived tensor and cohomology comparisons are explicit specializations of existing arbitrary-ringed-topos and exact-functor statements.

## Mathlib and duplicate searches

I searched the whole DAG by titles, Tor/localization keywords, and source tags (08G1, 08H5, 09C2, 098A), and ran `tools/blueprint_refs.py ancestor lem-sfb-proetale-tor-local-global` plus whole-blueprint searches for `Tor amplitude`, `tor-amplitude`, `ringed site`, `Tor intervals survive`, `finite affine refinement`, `098A`, `locally has finite tor dimension`, and `quasi-compact scheme`. The ancestor is `det-lem-integral-models-stacks`; none of the imported blueprint nodes duplicates this general equivalence. No new node was needed, so there is no new-node duplicate pair to resolve.

Mathlib searches were executed only through the prescribed msearch.py command. The two LeanFinder phrasings returned finite-type and finite-presentation sheaf facts, not Tor intervals; LeanSearch returned sheaf limits and projective dimension facts; Loogle's Tor/Sheaf pattern returned presheaf/Yoneda names; grep for Tor-amplitude and finite-Tor-dimension spellings returned no hits. I read all returned signatures. These do not imply the item in one specialization. Existing imported search records are retained, and all five new actual searches are appended with their exact tool/query strings and no-match verdicts.

## Not duplicates

No new nodes. `lem-pc-quasi-compact-finite-tor-dimension` concerns ordinary scheme structure-sheaf modules, not constant-coefficient pro-etale module sheaves. `lem-sf-site-tor-interval-restriction` supplies only preservation of a fixed interval under slice restriction and is cited. `lem-sfb-finite-affine-proetale-refinement` assumes Noetherianity and quasi-separatedness; it is not cited. `lem-sf-flat-model` imposes finite coefficient and constructibility hypotheses and is not cited. `lem-sp-ringed-site-tor-flat-model` is a general flat-model equivalence, not this local-to-global assertion; the proof does not need it. The general derived tensor comparison already exists as `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, so no comparison lemma is recreated.

## Tool uses

The split_report declares the general derived tensor pullback comparison, the arbitrary-ringed-site Tor interval restriction theorem, and the pro-etale topology description as tools. They supply generic identities and covering properties, rather than replacing any step of the integral-models unit. Exact restriction, derived restriction, exact-functor cohomology, localization, scheme and topology notions are closed results, Mathlib facts, or definitions. The unit's constant/completed coefficient distinction is preserved: throughout this item the ring is the constant ring sheaf A_X, with ordinary ambient derived tensor, never completed tensor.

## Review by Q05

I checked the source and every cited statement with the files open, against delivery-errors B through E. There are no statement-only new nodes to audit for B1-B8, and every used object is introduced in the item or the quoted definition. The item keeps its existing provenance and adds the precise blueprint use. No SGA source is used.

Step 1 uses `def-pur-localized-ringed-site` for the coefficient ring and sectionwise restriction, `lem-pur-site-restriction-module-adjunction-exact` for exactness of module restriction, and `def-weil-pbc-ringed-derived-restriction` for the induced functor on the unbounded derived category. The derived tensor comparison node explicitly allows arbitrary small ringed topoi and arbitrary unbounded derived objects. Applying it to the localization morphism is legitimate because its coefficient map is the identity, making module pullback restriction. Exactness identifies its derived functor with termwise restriction. The exact-functor cohomology statement explicitly gives H^q(FK) isomorphic to F(H^q K), in every integer degree. These give exactly the displayed formula, with no boundedness hypothesis. This is a specialization of existing comparisons, not a new comparison proved inline.

Step 2 uses `lem-sf-site-tor-interval-restriction`, whose conclusion explicitly quantifies over every module on the localized ringed site, and the identity-cover axiom of `def-weil-pbc-sites-and-cohomology`. Its site-size and commutative ring-sheaf hypotheses hold for the chosen small pro-etale site and A_X. This proves every clause of (2) for an arbitrary object U.

Step 3 uses the scheme definition and quasi-compactness to select finitely many affine open subschemes. The topology statement `sk-def-pe-site` explicitly says that Zariski coverings are pro-etale and that every cover of an affine target refines to a finite affine cover. The general site definition states composition of coverings. These are exactly the facts used, so the finite family covers in the site's topology, not just on underlying sets. Choosing a finite affine subcover and indexing its finitely many refinements is elementary from these statements. I corrected the potential use of the stronger Noetherian finite-refinement node before writing the split.

Step 4 applies the same Tor restriction theorem on the slice over each Z. The relocalization clause of `def-pur-localized-ringed-site` identifies the iterated slice and its restricted coefficients with the slice over V. No identification of a slice site with a separately chosen pro-etale site is needed. Taking minima and maxima is a finite integer calculation. Including 0 ensures that the extrema exist even for empty X, so a <= b is verified in every case.

Step 5 uses the module-restriction definition and the Tor-amplitude vanishing definition, together with the explicitly proved comparisons of step 1 and intervals of step 4. If q is outside the larger interval it is outside every smaller interval. N restricted to any V is a legitimate degree-zero module on that slice. No unmentioned descent or extension of modules is used.

Step 6 uses the base-change covering axiom and sheaf equalizer axiom stated in `def-weil-pbc-sites-and-cohomology`, and the sectionwise restriction formula of `def-pur-localized-ringed-site`. A section on any T restricts to zero on its covering pullbacks, so separatedness forces it to be zero. This proves F=0 as a sheaf rather than merely F(X)=0. The same argument works for empty X using the empty covering. Thus the selected interval works simultaneously for every global N.

I tested empty X (interval [0,0], every module sheaf zero), the zero ring, M=0, a field coefficient ring, a single local interval, and finitely many disjoint components with different Tor intervals. The inserted extrema and containment direction are correct. The argument also accommodates non-Noetherian and non-quasi-separated quasi-compact schemes because refinement is only invoked over affine targets. Without quasi-compactness an infinite disjoint union with shifts of nonzero constant modules in unbounded degrees gives the expected failure of a uniform interval; the proof uses quasi-compactness exactly where needed. All six steps are shorter than 2000 characters. Every non-elementary input is in a cited statement, and citations.json has one verbatim excerpt for every use. No proof is moved into a restatement node, no hidden induction is present, and no new assumptions are added.

## Unfinished work

None in the mathematical split. Delivery checks follow this report; any diagnostics will be repaired before push.

## Delivery validation

The first dry run rejected one citation excerpt as shorter than its 40-character minimum. I replaced it by the complete exactness-and-adjunction sentence copied from the cited statement; no mathematical change was needed.
