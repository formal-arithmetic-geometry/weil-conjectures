## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-scalar-tower-limit-square.json`: existing statement split in eight steps; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every node cited by every numbered proof step.
- `searches.jsonl`: six actual searches made with the required launcher command; all answered. The item retains its previous searches as well.

0 new nodes; 0 new Mathlib leaves. All mathematical ingredients were already in the DAG. Only the item node is delivered, with this report; the citation and search records are sandbox validation evidence.

## Attachments

None. A search of the entire project `lean/WeilConjectures/` for the exact blueprint tag returned no declaration. Searches by flat restriction, K-injective preservation, scalar/tower/limit terminology found ordinary scalar functors, specialized etale restriction, completed integral coefficient definitions, scalar extension, and module-object scalar coherence. Those do not give the arbitrary small-site, arbitrary ring-sheaf, unbounded derived strict-tower statement with its specified square. In particular `SixFunctors/ProEtale/CompletedIntegral.lean` constructs coefficient objects and restriction, rather than proving this square. Nothing was compiled and no Lean was written.

## WANTED

None. The blueprint and all Stacks passages used are present in the read clone.

## Findings and corrections

The item's statement is retained exactly. It was an unsplit agent-created supplement to the second paragraph of the current blueprint's completed-exchange coherence proof. That paragraph instructs conjugation by specified direct-image/limit isomorphisms but does not prove the scalar square. The delivery supplies that argument rather than asserting that any isomorphism of the endpoints suffices.

The statement dependency on `lem-weil-pbc-ringed-strict-tower-homotopy-limit` was added: it is the existing definition/computation of the strict total derived limit used here. No imported fields or provenance were removed. The chapter and unit records were read and kept unchanged; this is a node-level coefficient-comparison supplement, not a different route for a unit theorem.

The potentially misleading existing `lem-cbc-flat-scalar-direct-image-limit-coherence` states a related square with exact countable products as an extra hypothesis. It cannot be applied here. The proof instead uses preservation of K-injectives by right adjoints with exact left adjoints, avoiding that extra hypothesis. The generic `lem-weil-pbc-kinjective-exact-square-comparison` supplies exactly the normalized derived comparison needed for lambda and is reused rather than recreated.

No statement dispute was found. No required work remains apart from the dry run and delivery recorded below.

## Blueprint and duplicate searches

Read `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-completed-exchange-coherence.proof.md` in full. Ran `tools/blueprint_refs.py ancestor lem-weil-pbc-flat-scalar-tower-limit-square`, which identifies `lemma-weil-pbc-completed-exchange-coherence` as ancestor. Whole-blueprint searches for `scalar.*limit`, `scalar restriction`, and `K-injective`, plus whole-DAG keyword searches and Stacks-tag searches for 08BJ and 0A07, found no blueprint statement that replaces the item. The existing diagram scalar restriction, K-injective exact-square comparison, strict-tower limit, right-adjoint preservation, and direct-image/limit nodes are cited.

## Mathlib searches

The actual queries and digest-bearing responses are in `searches.jsonl` and are appended verbatim in the node's `mathlib_searches`. Two LeanFinder phrasings were tried before the absence verdict, together with LeanSearch, Loogle, and two source greps. The hits `SheafOfModules.restrictScalars`, `SheafOfModules.createsLimit`, and `SheafOfModules.hasLimit` concern ordinary scalar restriction and module-sheaf limits. Their source was read in `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` and `Limits.lean`. The second phrasing found the general derived-adjunction unit/counit lemmas in `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`; that source was read too. Those normalize derived adjunctions but do not assert the scalar/strict-derived-limit square. None is an exact match or one-line specialization for the item. Loogle answered with zero hits, not an unavailable service.

## Review by N5

I read delivery-errors B through E in full, the worker brief and stage-1 standard, the three blueprint levels in SETUP, GOAL, the item's chapter/unit, and the current blueprint passage. For the mathematical source I read Stacks `sites-cohomology.tex`, Tag 0A07 (`lemma-Rf-commutes-with-Rlim`), especially the first proof using the tower-topos square; `derived.tex`, Tags 070Y (`lemma-K-injective-defined`), 070K (`lemma-enough-K-injectives-implies`) and 08BJ (`lemma-adjoint-preserve-K-injectives`); and `sites-modules.tex`, Tags 04JC (`lemma-flat-pullback-exact`) and 03D7 (`lemma-adjoint-pullback-pushforward-modules`). The proof is explicitly marked agent-written: 0A07 and 08BJ are ingredients, not sources that already state the scalar square. There are no new nodes whose sources require separate review.

For step 1 I opened the statements of `def-pc-sheaf-restrict-scalars`, `def-weil-sheaf-of-modules-category`, and `lem-weil-pbc-flat-ringed-diagram-restriction`. The first fixes the same underlying abelian sheaf and the action through the ring map. The second gives sectionwise module and restriction data, so componentwise gluing proves the ordinary family limit directly. The third explicitly supplies exactness and K-injective preservation for restriction and identifies the ordinary direct-image comparison. It applies for both the tower category and the one-object category, so it gives both d and chi with the same normalization. The two coefficient pullback ring isomorphisms and their compatibility are exactly the item's hypotheses.

For step 2 I opened all four cited statements. `lem-weil-pbc-diagram-site-realization` gives a small ringed site and an exact additive equivalence, not merely an informal diagram identification. `prop-pur-kinjective-resolutions-exist` applies because the constructed site is small and its ring sheaf is commutative. The transport of the K-injective condition uses exactness and the explicit chain-homotopy equation. `lem-weil-pbc-kinjective-total-derived` says that K-injectives compute the universal total derived functor. `lem-weil-pbc-ringed-strict-tower-homotopy-limit` states exactly the strict diagram computation being used. Thus neither a large index category nor an unjustified resolution existence is hidden here.

For step 3 I checked the statement of `lem-weil-pbc-kinjective-exact-square-comparison` hypothesis by hypothesis. The top functors are additive ordinary limits; both vertical restrictions are exact; the source restriction preserves K-injectives; all source categories have enough K-injectives. The equality of composites is available with sectionwise compatible-family choices, and the ordinary family isomorphism identifies any other choices. That node's normalization equation is precisely the displayed lambda equation. This is a use of its statement, not a construction taken from its proof.

For step 4 I read the complete statements of the four cited nodes. `lem-trf-geometric-inverse-image-exact` is for arbitrary geometric morphisms and includes transported module actions, so it really applies to the small-site topoi here; the scheme-only exactness nodes would not suffice. The ring isomorphisms identify this with the L in the flat diagram lemma, which explicitly gives the required adjunctions. `lem-weil-tower-category-levelwise-abelian` gives exactness of termwise inverse image and constant diagrams. `lem-weil-pbc-right-adjoint-preserves-kinjective` gives the required preservation only after these exact left adjoints have been identified. For limit the adjunction is written out as compatible families. This checks precisely why limit I and the direct images can be used without further resolutions. No claim about exact countable products is used.

For step 5 I opened `lem-weil-pbc-right-adjoint-preserves-limits`: it identifies the preserved cone by its projections, so it justifies the ordinary beta maps with exactly the components used. The flat diagram lemma fixes delta as the identity ordinary comparison. I explicitly computed both n-th projections and checked that their equality is the naturality square for delta and the projection p_n. Uniqueness is used only for ordinary module limits, never for a homotopy limit in a derived category.

For step 6 I checked `lem-weil-ringed-tower-pushforward-limit-comparison` against the equation for kappa: its statement specifies the common underived direct-image composite and comparison with its total derived functor. The A and B maps in the proof are precisely its two composite universal units on the K-injective model. `lem-weil-pbc-kinjective-total-derived` makes these units invertible, and the statement of the flat diagram lemma fixes the unit-normalized d and chi. This avoids using a comparison with the same endpoints but a different normalization.

For step 7 I checked the source and target of each expression. After precomposition with r_V(A_I^S), both sides start at Q of r_V F_S lim I; both end by the same B^R_{r_UI}. The two maps remaining inside Q are the ordinary maps of step 5. The substitutions use only naturality, the three displayed unit equations, and inverse cancellation. This is an elementary calculation from preceding steps, not a separate comparison lemma hidden inline. Step 8 then uses naturality and an isomorphism to QI; no assertion about representing every derived arrow by an arbitrary strict chain map is necessary. It is likewise elementary. All proof steps are below 2000 characters.

I tested the identity ring change (rho, lambda, d, chi are the identity comparisons), identity u (the square reduces to the lambda naturality equation), zero towers, constant towers, and towers with zero transition maps. Each ordinary formula still preserves the actual compatible family and each derived formula is obtained through invertible units. Unbounded complexes and topoi without exact countable products are covered by the same K-injective argument; no product-exactness or boundedness assumption was silently inserted. The smallness and commutative-ring hypotheses are present wherever the resolution theorem is applied. I also traced every proposed proof dependency downward: none depends on this item, so the citations do not create a cycle.

The three generic off-unit tools are declared in `split_report.tool_uses`: arbitrary-geometric inverse-image exactness, small-ringed-site K-injective existence, and preservation of ordinary limits by a right adjoint. They supply generic tools for the fixed coefficient-comparison route. No unit step is replaced.

## Validation

The required `deliver.py N5 lem-weil-pbc-flat-scalar-tower-limit-square --no-push` exited successfully: `OK (not pushed)` at `977155a011a`, server preflight passed. The same delivery tool is now used for the authorized direct push. No Lean compilation or local DAG/preflight tools were run.
