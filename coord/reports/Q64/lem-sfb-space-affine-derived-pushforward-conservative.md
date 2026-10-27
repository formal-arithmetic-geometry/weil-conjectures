# Q64: lem-sfb-space-affine-derived-pushforward-conservative

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-derived-pushforward-conservative.json: statement, split into four proof steps; Mathlib searches find no matching algebraic-space theorem.
- citations.json: verbatim statements for every node cited in every proof step.
- searches.jsonl: actual search-command log, retained for delivery verification.

No new nodes and no Mathlib leaves were created. The mathematical statement and all seven statement dependencies remain unchanged.

## Attachments

None. The project declaration AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine in lean/WeilConjectures/AlgebraicGeometry/AffineDerivedPushforwardConservative.lean is the scheme result (blueprint lem-sc-affine-derived-pushforward-conservative), not the requested algebraic-space statement. Its type uses scheme module derived categories, not the small-etale algebraic-space categories. Searches for the assigned blueprint tag and for affine/conservative/reflects terminology under WeilConjectures found no exact project attachment.

## WANTED

None. All proof sources are available locally.

## Problems found and changes

The assigned node was unsplit and had no proof or proof dependencies. Its statement is correct against Stacks Tag 08II, with the landing assertion supplied by Tag 08FA. I preserved it. No released repair note or earlier sandbox split/report was present.

I first considered taking all locality and landing claims from lem-sfb-space-derived-etale-chart-calculus. Reading its statement rules that out: it gives etale direct-image base change, exact restriction, derived pullback preservation and locality of quasi-coherent cohomology, but does not assert that general derived pushforward preserves quasi-coherent cohomology or that restrictions jointly reflect derived isomorphisms. The final proof instead uses the existing qcqs scheme preservation theorem for landing, and writes out the gluing of local cohomology inverses for reflection. This repairs both potential C4 errors without adding nodes.

The current blueprint under literature/blueprint/latest was read, including sk-thm-sf-ctf-stability/_section.md. This item is an existing supporting algebraic-space coherent-derived tool deep below the imported constructibility argument, not the unit's key theorem. Its existing blueprint.from has node null and an explicit source-route place. The ancestor command likewise returns None. I retain that provenance rather than inventing an imported blueprint node. Searches of blueprint_refs for affine derived, affine morphism, derived quasi-coherent, 071Q, 08GH and etale localization found no second blueprint statement of this algebraic-space item. same_as remains empty. Chapter/unit records were read and left untouched.

## Not duplicates

No new nodes were created. The existing scheme theorem differs from the item in that its spaces are schemes and its derived module categories are Zariski ones. The existing scheme-derived etale comparison is cited to bridge that distinction; the distinction is not silently identified. The broader existing algebraic-space coproduct theorem would supply landing for qcqs morphisms, but is unnecessary: landing is proved locally using existing scheme preservation and etale comparison.

## Review by Q64

I read spaces-perfect.tex Tag 08II (lemma-affine-morphism) and the surrounding Tag 08FA (lemma-quasi-coherence-direct-image). The source reduces etale locally to schemes through Tag 071Q (lemma-derived-quasi-coherent-small-etale-site) and Tag 08GH (remark-match-total-direct-images). I read the equivalence and the two direct-image diagrams there. I also read perfect.tex Tag 08I8 (lemma-affine-morphism), Tag 08D5 (lemma-quasi-coherence-direct-image), spaces-morphisms.tex Tags 03WG and 03WI, morphisms.tex Tag 01S7, and the derived.tex Tag 05RT cohomology criterion. There are no new-node sources to review.

Step 1 uses exactly the affine locality statement of lem-sfb-space-affine-locality to obtain a scheme cover and an affine scheme base change; lem-trf-space-fibre-products-etale-covers says explicitly that the pulled-back covering is jointly surjective etale. The statement of lem-sfb-space-derived-etale-chart-calculus gives both preservation by derived pullback and the natural isomorphism a^*Rf_*K = R(f_V)_*b^*K. Thus the local source objects are in the required quasi-coherent category. The atlas may be non-quasi-compact and may be a disjoint union; nothing in this step assumes otherwise.

Step 2 uses lem-weil-pbc-affine-morphism-permanence, whose clause (3) says that an affine scheme morphism is qcqs. This checks the exact hypothesis in both lem-sfb-scheme-derived-etale-qcoh-comparison and lem-pc-derived-direct-image-preserves-qcoh. Their statements give, respectively, the unbounded canonical direct-image comparison and the preservation theorem. The chart-calculus statement then detects quasi-coherent cohomology on the cover of Y. This establishes the landing clause without assuming the spaces themselves qcqs.

Step 3 uses the same natural etale base-change comparison on the actual morphism u. The scheme-comparison statement gives an equivalence on each side and a natural isomorphism of direct-image functors; hence invertibility transports to the Zariski scheme direct image. lem-sc-affine-derived-pushforward-conservative states precisely the scheme reflection assertion for an affine map. Equivalences reflect and preserve invertibility simply by applying a quasi-inverse to an inverse. No finite-type, flatness, boundedness or Noetherian condition is introduced.

Step 4 uses only the exactness of etale restriction from the chart-calculus statement to commute restriction with kernels, images and cohomology. The step does not cite quasi-coherence locality as an isomorphism-locality theorem. Instead it explicitly glues the unique local inverses of the cohomology sheaf maps, using the sheaf axiom on each test object's pulled-back cover. Finally lem-weil-pbc-unbounded-derived-iso-cohomology is stated for an arbitrary abelian category and its unbounded derived category, so it applies to these module sheaves with no boundedness restriction. All these cited node statements were opened and their exact text is in citations.json.

I checked the B--E checklist: all non-elementary inputs are existing cited statements; no definition is substituted for a theorem; source tags and labels are given; no new lemma restates a clause; no new unsplit proof is hidden in a statement; existing metadata and searches are retained; all uses equal the proof-dependency union. Each proof step is below 2000 characters. I checked that the transitive dependencies of each input do not return to this item. Generic off-unit tools are explained in split_report.tool_uses rather than setting the maintainer-owned tool_uses field.

For small cases: identity affine maps give the identity reflection assertion; X empty gives the zero source category; Y empty forces X empty and the empty cover still detects the unique sheaf maps. Arbitrary non-Noetherian rings and unbounded complexes are allowed by each cited derived statement. No intersection of affine opens is presumed affine and no unjustified finite cover is chosen.

Mathlib searches were run through msearch.py with the actual results retained: LeanFinder twice, Loogle, source grep and LeanSearch. LeanFinder returned ordinary module forgetful functors or affine inverse-limit section lemmas; LeanSearch returned scheme affine-morphism geometry; Loogle and the targeted grep had zero hits. None states affine derived conservativity for algebraic spaces or supplies the entire item by specialization. Historical creation searches were preserved as required.

The server review_split check passed before the report was written. The required delivery dry run and push are the remaining validation/delivery actions, with their result recorded by the delivery tool.

## Unfinished

No mathematical part remains in this stage-1 split. No Lean was written and no compiler or Lake command was run. The maintainer's independent mathematical review follows delivery.
