1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-topological-filtered-cohomology.json`: repaired statement and six proof steps; no Mathlib match for the full theorem.
- `dag/nodes/sec-curve-estimates/lem-sc-topological-filtered-injective-cech-acyclic.json`: statement-only intermediate node; no Mathlib match.

2. Attachments:

- `CategoryTheory.IsGrothendieckAbelian.instHasFunctorialFactorizationMonomorphismsRlp` belongs to `lem-weil-pbc-grothendieck-functorial-injective-embedding` (existing Mathlib leaf).

3. WANTED: none.

4. Repair summary: the first version incorrectly used the sheaves-of-sets section-colimit node for an abelian-sheaf filtered system, left stalk and colimit-existence facts uncited, omitted injective derived-functor vanishing, and introduced a node already supplied by Mathlib. Step 1 now treats the system as indexed by the directed set in the statement, cites `lem-weil-pbc-module-directed-colimit-underlying-sets`, and writes the finite-refinement argument (Topology 0069(3)) explicitly. Step 2 cites the existing Grothendieck functorial-injective Mathlib leaf and the sheaf Grothendieck instance. Step 3 cites `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` for sheaf colimits and exact filtered colimits, `lem-weil-pbc-presheaf-module-stalk-filtered-colimit` and `lem-weil-pbc-module-stalk-filtered-colimit` for stalks, and `lem-weil-pbc-module-stalk-exact` for the stalkwise exactness criterion. Step 5 cites `lem-weil-pbc-derived-functor-injective-vanishing` and defines open cohomology as `R^q Gamma(U,-)` on the open-site abelian-sheaf category. The functorial-injective node created by the prior delivery was deleted because the existing Mathlib leaf states the generic result.

## Review by F1

I reread Stacks Cohomology Lemma 01FF and its proof, Sheaves Lemma 009F, Topology Lemma 0069(3), and Injectives Theorems 079H/01DI. The item statement now includes the directed-set hypotheses and explicitly defines `H^q(U,-)` as `R^q Gamma(U,-)` for the open site, matching the site cohomology definition. Step 1 uses the existing module underlying-sheaf colimit statement only for a directed set; the finite common-refinement and equality-at-a-later-index argument is written as the elementary part. Step 2 uses the existing generic Grothendieck functorial-injective statement; Mathlib's sheaf `IsGrothendieckAbelian` instance supplies its hypothesis. Step 3's cited statements respectively provide existence and exactness of sheaf filtered colimits, stalk filtered-colimit identification, stalk exactness, and exact filtered colimits of abelian groups; the constant ring sheaf `underline Z` supplies the ringed-space specialization. Step 4 retains the separate statement-only filtered-injective Cech-acyclic input and the Cech-to-derived criterion. Step 5 now cites both the universal long exact sequence and the injective-vanishing theorem, and says exactly which open cohomology functor is used. Step 6 is the elementary surjectivity/injectivity characterization of a filtered colimit map.

I checked the cited node statements verbatim when writing `citations.json`, verified every citation is present in `proof_deps`, and removed the duplicate Mathlib-covered node. Edge cases checked were q=0, the empty open, the zero sheaf, a one-point space, and a constant filtered diagram. The item and the remaining new node have the required blueprint references and recorded LeanFinder, Loogle, grep, and LeanSearch searches; LeanSearch was unavailable and is recorded as such.

## Not duplicates

lem-sc-topological-filtered-injective-cech-acyclic vs lem-sc-topological-filtered-cohomology: the new node is the Cech-acyclic intermediate for filtered diagrams of injectives, while the item asserts the final cohomology comparison for arbitrary sheaves.
lem-sc-topological-filtered-injective-cech-acyclic vs lem-weil-pbc-module-cech-vanishing-basis: the new node is for topological abelian sheaves and filtered injectives; the existing node is the module-site Cech criterion.
lem-sc-topological-filtered-injective-cech-acyclic vs lem-weil-pbc-scheme-modules-coproduct-finite-subsums: the new node asserts Cech acyclicity of a filtered colimit of injective sheaves; the existing node concerns finite subsums of coproducts of scheme modules.
lem-sc-topological-filtered-injective-cech-acyclic vs lem-weil-pbc-qcqs-cohomology-direct-sum: the new node is a Cech-vanishing input for filtered injectives on a topological space; the existing node is a direct-sum cohomology comparison.
lem-sc-topological-filtered-injective-cech-acyclic vs lem-weil-pbc-qs-scheme-cohomology-directed-colimit: the new node is the injective Cech intermediate for abelian sheaves on an open site; the existing node is the full directed-colimit theorem for scheme O_X-modules.
lem-sc-topological-filtered-injective-cech-acyclic vs lem-weil-pbc-scheme-modules-functorial-injective-embeddings: the new node concludes Cech vanishing for a filtered colimit; the existing node only constructs a functorial injective embedding diagram for scheme modules.

## Second reading by F1

Item statement: checked against Stacks Cohomology Lemma 01FF hypothesis-by-hypothesis; the directed index, quasi-compact basis, quasi-compact intersections, and sectionwise cohomology conclusion agree (with abelian sheaves as the constant-ring specialization).
Step 1: checked against Sheaves Lemma 009F parts (2) and (4); replaced the O_X-module underlying-set citation with the existing general sheaf sections theorem and made the finite-refinement argument explicit.
Step 2: checked against the injective-embedding paragraph of Lemma 01FF and the cited Grothendieck and abelian-sheaf definitions; the functorial diagram and cokernel sequence are stated by the citations.
Step 3: checked against the short-exact-colimit paragraph of Lemma 01FF; removed inapplicable ringed-space stalk citations and used the existing exact filtered-colimit theorem directly.
Step 4: checked against Lemma 01FF's Cech claim and Lemma 01EW; the finite quasi-compact covers, filtered Cech terms, and Cech-to-derived criterion match the hypotheses.
Step 5: checked against the displayed long-exact diagram in Lemma 01FF; expanded the connecting-map surjectivity and eventual-zero argument, including the separate degree-one section case.
Step 6: checked against the filtered-colimit characterization; the stated surjectivity and eventual-zero conditions are exactly the canonical-map isomorphism criterion.
New node lem-sc-topological-filtered-injective-cech-acyclic: checked against Lemma 01FF's claim and Lemma 01EW, with definitions cited for filtered diagrams, Cech complexes, and topological cohomology; statement-only form and three Mathlib searches satisfy B1-B7.

Changes: replaced the Step 1 module citation with the general sheaf sections node; removed three mismatched stalk/module citations from Step 3; wrote the Step 5 connecting-map chase instead of saying “diagram chase”; added the filtered-diagram definition citation to the Cech intermediate; synchronized citations.json with these repairs.
