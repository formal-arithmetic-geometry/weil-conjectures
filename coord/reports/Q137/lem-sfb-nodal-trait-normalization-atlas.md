## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-trait-normalization-atlas.json: statement item, split into fourteen assembly steps using existing nodes. Mathlib verdict: no match.
- citations.json: one entry for every proof-step citation, quoting the complete cited statement to keep all the clauses used visible.
- No new nodes; no Mathlib leaves; no unit record changed.

## Attachments

None. Searched the live project's WeilConjectures source for the exact blueprint tag, nodal, normalization atlas, and the local equations. The nodal mentions found are examples in six-functor files; no declaration states the item. Relative-normalization declarations are not this absolute componentwise-normalization theorem.

## Wanted literature

None. All source material used is present in literature/stacks-project/. The de Jong PDF mentioned by a neighbouring node was not used.

## Findings and corrections

The imported item had a statement but no proof. Its statement is retained exactly. This is an assembly using the existing split-node/conductor algebra, binomial Laurent-intersection normality, DVR local form, and smooth-pullback normalization. It needs no new node: making another nodal atlas or normalization lemma would duplicate these ingredients or restate the item.

The current blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), its unit, and the chapter were read. The item is a pre-existing geometric prerequisite below that route, not a literal theorem of the current blueprint. blueprint_refs ancestor returns None. Whole-blueprint searches for normalization and nodal found no matching imported statement. The existing blueprint provenance and unit were preserved.

A possible convention error was avoided: finite morphisms are projective in the bundle sense, whereas def-kun-projective requires an embedding in finite projective space. Step 13 explicitly composes in the bundle sense and uses the ample structure sheaf on the affine trait to obtain H-projectivity. Another possible gap was avoided: normality of C does not imply geometric reducedness of its fibres or generic smoothness over an imperfect field. Steps 10--12 prove these using the actual local models, including generic split nodes over finite separable extensions.

## Not duplicates

No new nodes were created. Reused lem-sfb-dvr-nodal-etale-local-form (0CDD), lem-sfb-componentwise-normalization-smooth-pullback (07TD), lem-sfb-split-node-normalization-conductor (035P/0CDV), and lem-sfb-binomial-laurent-normal-form. The stronger smooth-generic nodal-trait normality theorem cannot replace normalization of a family with persistent nodes, since its smooth-generic hypothesis is absent here.

## Review by Q137

I read models.tex lemma-etale-local-at-worst-nodal, Tag 0CDD, statement and proof: it allows arbitrary DVRs and both uv=0 and uv=pi^n, including n=0. I read curves.tex lemma-etale-local-structure-nodal-family, Tag 0CBY, statement and its proof, and the source-local and postcomposition lemmas at 0C5D and 0CD8. I read more-morphisms.tex lemma-normalization-and-smooth, Tag 07TD, including its finite-component hypothesis and proof. Locally Noetherian schemes satisfy the hypothesis through the existing smooth-pullback node. I also read morphisms.tex 035Q, the Noetherian finite-type lemma, the etale-open lemma, and 0B3I/0C4P/087S on projectivity. These sources do not assert this global item verbatim; proof_origin is therefore agent, as required. There are no new nodes needing separate source verification.

For step 1 I opened the statements of finite-type-over-Noetherian, the geometric-reducedness algebraic-closure test, the affine flatness criterion, flat-module torsion-freeness, and affine fibre products. They supply Noetherian X, reduced X_K, flat B and injectivity into B[1/pi]; I wrote the nilpotent argument rather than assuming reducedness of the total space. R is a domain and Noetherian because it is a DVR. No geometric-fibre assumption was replaced by ordinary reducedness.

For step 2 I checked the exact hypotheses and conclusion of dvr-nodal-etale-local-form, including the point above each special-fibre point. Affine restriction preserves both etale maps. For step 3 I checked nodal-family-etale-local-model, etale-fibre-discrete-separable-points, and nodal-model-etale-smooth-locus: the last really says that the parameter vanishes at the chosen nonsmooth point, so over a field it is zero. Etale field neighbourhoods split into finite separable fields, not arbitrary algebraic extensions. Open immersions and etale composition are supplied by etale-composition-cancellation. All generic charts remain etale as maps to X.

For step 4 I checked that etale-morphism-open-map says images are open and used the finite-subcover argument on Noetherian X. Each affine chart is Noetherian, which verifies quasi-compactness of its map to X even though it need not be finite. The cover used for finite descent is finite, flat, surjective and quasi-compact.

For step 5 I opened componentwise-normalization-generic-properties and componentwise-normalization-smooth-pullback, not just their definitions. The former actually supplies integral surjectivity; the latter supplies the isomorphism over the original scheme, without assuming finite normalization or excellence. Both source and target of every application are locally Noetherian. Step 6 uses the full split-node-normalization-conductor statement, which explicitly identifies the finite normalization algebra and the smooth branches for both a field and a DVR. The etale-base-change node is used only for its stated pullback-etaleness clause.

Step 7 uses the normal-domain and prime-localization clauses of binomial-laurent-normal-form with the nonzero parameter pi^n. This includes n=0; uv=1 is smooth and normal. I wrote why a DVR is integrally closed, so no excellence or completion assertion enters. The normal-domain identity clause is explicitly present in split-node-normalization-conductor. Step 8 uses integral-normal-generic-recognition on an identity map, verifying integrality, the generic-point bijection and residue-field identities. Smooth-normal-ascent applies over the normal field K, and smooth-trait-curve-local-properties supplies normal local rings on the relative smooth locus over R. Restriction of normalization is an instance of the actual smooth-pullback statement.

For step 9 I checked that finite-morphism-fpqc-descent states finiteness for a flat, surjective, quasi-compact base change, with all three hypotheses verified in step 4. Base change of the finite split algebra is proved directly with its finite generating set and the affine tensor-product formula, rather than using an uncited descent theorem. Steps 10 and 11 use the normalization chart cover of C. Nodal-family-etale-source-locality supplies flatness, local finite presentation and the nodal condition; scheme-nodal-etale-postcomposition supplies passage from R_a or K_a to R. I separately checked geometric reducedness: identity charts inherit it by etale-proposition-etale-reduced; smooth branch charts have normal local rings over an algebraically closed field; flat-local-hom-faithfully-flat and faithfully-flat-universally-injective give the injective stalk map needed to descend reducedness. None of these citations is merely a definition standing in for descent.

For step 12 I checked that binomial-geometric-fibres actually says a nonzero-parameter hyperbola is smooth over its coefficient field. Smooth-composition and etale-source-smoothness then give smoothness of C_K, even over imperfect K. Etale-fibre-discrete-separable-points supplies separability of Frac(R_a)/K; normalization of X_K comes from smooth pullback along its open immersion, not arbitrary base change. For step 13 I checked finite-projective-bundle, projective-bundle-composition, projective-bundle-to-h-projective, and projective-bundle-relative-ample against their exact conventions. The affine base has an ample structure sheaf by the definition, taking section 1. The local finite presentation conclusion becomes global finite presentation after quasi-compactness and quasi-separatedness. Step 14 writes the field tensor-product argument that preserves surjectivity on geometric fibres, so nonempty fibres are actually proved.

I tested the smooth projective line, the persistent-node family formed by two projective lines meeting along a section, a disjoint union of nodal families, n=0, n=1, n=2, and n>2 in uv=pi^n, a nonsplit node before finite separable etale extension, and an imperfect generic ground field. uv=0 must separate; uv=pi^2 must remain unchanged and can keep a nodal special fibre. No connectedness, perfection, excellence or completeness was added. An empty whole family is excluded by the item's nonempty-fibre hypothesis, while individual charts may have empty fibres. The report and proof distinguish these cases.

I checked delivery-errors B--E: all introduced objects appear in existing statements, no statement-only node conceals a proof, no elementary lemma or clause of the item is relabelled as a new node, every used non-elementary fact is a node citation, and quotations are literal statement text. I read the recorded Mathlib results: relative normalization and Weierstrass reduction do not prove this item, and a second semantic phrasing gave the same mismatch. All new searches are taken from the msearch log without invented queries. All proof steps have fewer than 2000 characters. No stage-2 work, compiler, or repository write was performed.

## Unfinished work

None in the stage-1 split. The ordinary queue retains the existing unsplit dependencies; this delivery does not split those nodes again. Server dry-run and push results follow in the delivery command output.
