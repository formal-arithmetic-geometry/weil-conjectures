# Stage-1 worker report: lem-sfb-closed-test-scalar-model-coherence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-test-scalar-model-coherence.json`: the existing statement, unchanged; nine complete proof steps, status split. No new nodes and no Mathlib leaves.
- `citations.json`: 27 verbatim statement quotations, one for every step/node citation.
- `searches.jsonl`: actual output records of the required search command; the original item's five earlier search records are retained in its JSON. The new records are appended without inventing searches.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not part of the DAG delivery.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, closed_test/closedTest/ClosedTest and scalar/derived restriction terminology. No project declaration states all clauses of this item. The étale `SixFunctors/BaseChange/DerivedRestrictScalars.lean` proves a related bounded-below discrete-coefficient theorem, not this internal condensed-coefficient closed-test normalization. `ScalarForgetPullbackAdjunction.lean` concerns Zariski sheaves over a field, also a different statement. The Sheaf declaration attached to the parent is source material, not an attachment for this item.

## WANTED

None. The Stacks sources needed for the formal derivation are available locally. The closed-test/scalar assembly is explicitly agent-written, rather than attributed verbatim to a Stacks lemma.

## Corrections and scope

The statement is retained exactly. There is no blueprint_update or released repair note for this item and no previous sandbox split or report. The empty proof needed an argument; its source's mention of 09T5 alone does not establish scalar/model compatibility.

The main type issue to guard against is the direction of the comparisons. Both delta and gamma point from the scalar-restricted primed derived result to the derived result of the restricted input. For an actual map alpha: K -> Res N, the coefficient diagrams are cospans through the model of Res N. Step 8 writes these cospans explicitly. It never invents a map from the K-model to the N-model by reversing gamma. This is an explicit reading of the original direction and naturality requirement, not a changed hypothesis or conclusion.

The ring-sheaf change-adjunction node happens to provide a stronger isomorphism statement. We take only its forward comparison and its adjunct equation. The proof neither assumes restriction preserves K-injectives nor inverts the derived scalar comparison, and adds no invertibility assertion to the item. On a primed K-injective model, the unprimed restricted model is separately resolved. The final input is the ordinary unit M[0] -> Res(S tensor_R M)[0], with no substitution of a derived tensor unit.

## What remains

No part of the item's proof remains unaccounted for. Existing cited nodes retain their own proof obligations; this worker creates none. Required server dry run and direct push follow this report.

## Blueprint and duplicate searches

Read the chapter `sec-six-functors-basics`, unit `sk-thm-sf-ctf-stability`, its direct-images proof in the main-20261015 blueprint, and the parent `lem-sfb-closed-test-derived-exchange-model`. This item is the scalar-coherence obligation extracted from the parent's returned steps 10--11, along the inherited paragraph (3) route. The ancestor command reports `blueprint.from.node = None`; retained that exact inherited ancestry and its via chain. Whole imported-blueprint searches for `scalar model` and `coefficient comparison` returned respectively zero and 45 candidates. Their restricted six-functor and scalar-extension statements do not state this arbitrary condensed-coefficient closed-test lemma. Thus same_as remains empty.

Searched the whole DAG by scalar restriction, right-derived comparison, adjunction, square, and closed-test terms, and read the statements of the exact-square, scalar-adjunction, internal/section, closed-test and slice-localization nodes used below. No new node was needed: the non-elementary formal facts already have nodes. In particular the exact-square right-derived-unit node suffices for constructing delta/gamma; the ring-sheaf change-adjunction node supplies the adjunct identity, and the four sibling closed-test nodes supply the actual unit, models, chain-mate and within-coefficient naturality. No elementary fact or clause of this item was turned into a node.

## Not duplicates

No new nodes; no new/existing same-tag pairs to distinguish.

## Mathlib searches

Ran leanfinder, loogle, grep and leansearch with the exact queries recorded by msearch in searches.jsonl, and a second leanfinder phrasing about a canonical right-derived comparison and adjunction mates. All five searches returned successfully. Loogle's `"rightDerived", "restrictScalars"` had zero hits. The grep hits were ordinary module scalar units, base change and tensor products. LeanSearch found ordinary ModuleCat and SheafOfModules restriction constructions. LeanFinder found the generic derived adjunction normalization equations and LocalizerMorphism.rightDerivedFunctorComparison. Read Mathlib's `CategoryTheory/Functor/Derived/Adjunction.lean`, including derivedη_fac_app and derivedε_fac_app; these are factors of the proof, not a one-line theorem about closed-test models with arbitrary condensed rings. They do not cover the unit-section inverse, localized section identities and arbitrary actual-map naturality clauses. The item is therefore split, not a Mathlib leaf. No new node needs a separate search record.

## Review by O2

I read delivery-errors B--E in full and checked the item against the cited statements, not against the cited nodes' proof text. I used Stacks derived.tex 09T5 (`lemma-derived-adjoint-functors`), 070Y (`lemma-K-injective-defined`) and 070I (`lemma-K-injective`); sites-cohomology.tex 07A6 (`lemma-adjoint`), 0D6E (`lemma-derived-pushforward-composition`), 0D6F (`lemma-unbounded-cohomology-of-open`) and 0FPI (`lemma-adjoints-push-pull-compatibility`); proetale.tex 09BL (`lemma-closed-immersion-affines-apply`), including the proof of evaluation on weakly contractible objects; and sites-modules.tex `lemma-pullback-module`, `lemma-adjoint-push-pull-modules` and the tensor-product construction. There are no new-node sources and no SGA sources.

Step 1 uses coefficient-morphisms' actual statement that alpha_b is the component of the pullback-from-point natural isomorphism. This holds for an arbitrary condensed ring, unlike the narrower list of admissible rings in another Cartesian-coefficient proposition, which I deliberately did not cite. The internal-section scalar-adjunction node identifies restriction without changing underlying sheaves, and section-derived-pushpull-normalization identifies the specified adjunctions, resolution transformations and compositors. The universe and monoidal-sheaf hypotheses are exactly those of the item's small pro-etale sites and the already supplied internal module categories.

Step 2 uses the exact-square right-derived-unit node with the displayed F,G,U,V. Restriction is exact by clause 4 of change-of-scalars. Output restriction for delta is exact; for gamma the output category is Ab and the output functor is the identity. The ordinary identities are the section identities in the item. Existence of K-injective resolutions is part of the item's ordinary derived module setup. The node explicitly says K-injective preservation and invertibility are unnecessary, and specifies the universal unit equation. The right-derived definition gives uniqueness and how to compute after separately resolving Res J. Thus this step has the correct direction, not the more tempting reverse direction.

Step 3 uses the actual statement of ring-sheaf-change-adjunction: identified-coefficient inverse image, the derived comparison induced by the equal composites, and its formula for taking adjuncts. Step 1 verifies its ring-map compatibility. Its comparison is the same normalized derived comparison as in step 2, by the universal property in right-derived-functor. Substituting the identity and the counit into the supplied adjunct equation yields precisely the two displayed unit/counit equations, with the canonical pullback identification suppressed. We use the forward morphism only; no claim about Res J being K-injective is smuggled in through the stronger theorem.

Step 4 uses coefficient-morphism naturality, the internal-section scalar comparison and section-derived-pushpull normalization for the compositors. The ordinary scalar/pullback squares have the same underlying inverse-image map and coefficient action, so the written identity proves their coherence before termwise exact descent. For sections, unbounded-sections-localization explicitly states that its map is the degreewise identity I(W)=(I|W)(id_W); uniqueness of the derived comparison proves gamma's localization square. I also explicitly included the direct-image localization square for delta, using ringed-derived-slice-localization, whose statement supplies precisely that canonical square and its unit/counit compatibility. Applying both paths to computation units gives the same ordinary section identity. This avoids using a definition of localization as though it were a derived comparison theorem.

Step 5 is a categorical substitution using the adjunct equations of step 3 and the actual exchange formula stated in closed-test-chain-mate-restriction. I checked the common source s_R^* Res Rf'_* N and common target R(f_Z)_{*,R} h_R^* Res N. Naturality of delta first moves it through the counit-square composite; the counit, compositor and unit equations give the stated equality. This is marked elementary because the non-elementary adjunction compatibility and exchange identification are cited, leaving only that explicit substitution. No invertibility of exchange is needed.

Step 6 uses closed-test-unit-evaluation for the actual unit and its inverse, and closed-test-kinjective-section-models for precisely the normalized two section complexes. Its hypotheses include both V and B being w-contractible, exactly as assumed. Equality on a section x proves the underived scalar square; the derived computation-unit equation then gives the model square. Only the actual closed-unit isomorphism is inverted. Unbounded-sections-localization identifies the same models by degreewise section identities, so the localized squares have those normalizations as well.

Step 7 uses chain-mate-restriction's statement that the localized chain arrow Q(j(T0) eta_a) is the specified derived unit/composition restriction, and the two normalized model isomorphisms from kinjective-section-models. The proof pastes those isomorphisms around the explicit exchange equality to give gamma_T0 r_S = r_R gamma_T. It cannot use the item's own statement, the parent's proof, or a node merely restating this coefficient clause: every cited sibling concerns a single coefficient system.

Step 8 uses within-coefficient closed-test-localized-model-coherence for all derived maps, including resolution independence. Since Res is exact, Res N stays bounded below. K-injective-hom-derived gives the unique homotopy class after a separate unprimed resolution of Res N, so arbitrary derived maps, rather than just strict module maps, are covered. I wrote both cospans to check the types and to avoid the incorrect reverse coefficient arrow. Naturality of the scalar comparison in N and naturality of the unprimed model in alpha provide the whole mixed diagram.

Step 9 uses the ordinary scalar-adjunction unit explicitly stated in internal-section-scalar-adjunction, together with change-of-scalars' ordinary extension. An ordinary tensor module in degree zero is bounded below even for a non-flat coefficient map. No tensor-exactness or derived comparison assertion is used.

Small cases checked: a=0 makes s and a identities; the normalization equations reduce to ordinary naturality and identity units. For a=A, V is empty and every displayed closed-test model/arrow is the zero object/arrow; the same is true for A=0 or empty X. The identity coefficient map gives the identity normalized comparison. Lambda'=0 has only the zero primed module and all scalar naturality diagrams reduce accordingly. Non-flat maps, for example the constant condensed map Z -> Z/2, still have exact restriction, and the proof separately resolves a restricted injective instead of calling it injective. The ordinary tensor unit remains a degree-zero map, even though a derived tensor could have extra negative homology. There is no properness, finite-type, flatness, uniform bound or acyclicity hypothesis added. None of the nine steps exceeds 2000 characters; no long step hides a new lemma. Proof dependencies are exactly the union of uses, and citations.json contains a verbatim quotation for each pair.

## Validation

The first dry run rejected the short quotation of scalar-restriction exactness (under 40 characters). Replaced it with the full exactness clause for steps 2 and 8 and the ordinary scalar-extension clause for step 9. Also expanded the model, exchange, exact-square and localized-direct-image quotations to include their actual displayed formulas. The proof and statement did not change.
