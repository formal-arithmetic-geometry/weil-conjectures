# Stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-derived-base-change-vertical-pasting.json: statement, split; Mathlib has categorical pasting and underived module comparisons, but no exact scheme O-module derived base-change pasting theorem.
- citations.json: verbatim statements for all eleven step citations.

No new nodes and no new Mathlib leaves. No Lean was written or compiled.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint id and for vertical pasting, derived base-change composition and schemeDerivedBaseChangeMap. The exact id has no declaration. The etale/pro-etale constant-coefficient and lower-shriek pasting declarations concern other operations/categories. SchemeDerivedMateEvaluation supplies evaluation for one square, not this two-square identity.

## WANTED

None. Stacks cohomology.tex and sites-cohomology.tex contain the needed sources.

## Issues found

The source Tag 0ATL (remark-compose-base-change) explicitly omits the verification. The item is true as stated; its statement and statement dependencies are unchanged. The split supplies that missing verification rather than citing 0ATL as a black box or introducing a restatement node. Quasi-compactness and quasi-separatedness are used only to put Rf_*E in D_QCoh so the bottom application of the node's stated base-change definition is permitted.

The existing blueprint.from.node is null. tools/blueprint_refs.py ancestor reports exactly that: the existing created.item chain does not reach an imported blueprint node. I preserved the chain and its detailed place, and recorded the current latest blueprint path in split_report, rather than inventing an ancestor. The current chapter and unit, their DAG records, and latest sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md were read. Paragraph (3) is the direct-image route served by this prerequisite; no chapter or unit record was changed.

## Not duplicates

No new nodes. The existing lem-weil-pbc-mate-pasting is a general categorical Mathlib leaf; lem-pur-ringed-derived-composition-cocycle supplies the coherence needed here. sbc-lem-identity-and-base-change-composition, sbc-lem-base-change-composition and the existing etale exchange results concern constant coefficients and/or composition in the other direction, so are not exact attachments for this O-module statement. No duplicate was introduced.

## Mathlib and blueprint searches

Read all five actual search results in searches.jsonl. The first LeanFinder query found underived Scheme.Modules.pullbackComp, pushforwardComp and pseudofunctor_associativity; the second found exponentiable-morphism units and underived sheaf pushforwards. Loogle returned zero hits for the comma-separated mate names. The grep located CategoryTheory.mateEquiv_vcomp at Mates.lean:170 and mateEquiv_hcomp at :209 and their bicategorical counterparts; their source was read. LeanSearch returned pullback pasting, IsBaseChange.comp and linear-map base change, not the derived scheme theorem. Thus this item is not a one-line Mathlib specialization: its specified geometric derived maps must still be identified and compared. The search for the second phrasing also ran and was read; no unavailable service is misreported as absence. Preserved the item's inherited grep entry and added exactly the newly logged queries.

Searched the whole DAG by tag and keywords, then statements for categorical pasting and direct-image coherence, and ran blueprint_refs.py search for base change, derived/compose/base, and direct/image/composition. Existing nodes supply all ingredients. No proposed node survived the elementary/duplicate/Mathlib tests because none was needed.

## Review by NV

I read cohomology.tex Tag 0ATL (remark-compose-base-change, lines 6673 onward) for the item, Tag 08HY (remark-base-change) for the map, Tag 079W (lemma-adjoint) for the Hom bijection, and Tag 0D5T (lemma-derived-pushforward-composition) for its adjoint-normalized canonical comparison. The Tag 0D6E proof in sites-cohomology.tex gives the same canonical derived composition on ringed topoi. I opened the full statements of every cited node; citations.json copies them verbatim, including the formulas actually used.

Step 1 uses def-pc-fibre-product, which states the universal property with uniqueness: the explicit two lifts establish the outer pullback. It uses lem-pc-derived-direct-image-preserves-qcoh with precisely f quasi-compact/quasi-separated and E in D_QCoh. The item supplies both hypotheses. No assertion that an arbitrary scheme is affine, no Tor assumption, and no boundedness hypothesis occurs.

Step 2 uses lem-pc-derived-direct-image-composition for the actual canonical isomorphisms, def-pc-derived-direct-image for their ringed-space interpretation, def-weil-pbc-ringed-topos-morphism for the ringed-topos setting, and lem-pur-ringed-derived-composition-cocycle for the associativity equality. The sites of open subsets are sets in a universe containing the schemes; this is not an illicit application to a large index category. Module pushforward on these topoi is exactly the usual ringed-space pushforward. The cocycle node applies to arbitrary ringed-topos morphisms, with no exactness or cartesianness condition, and states the displayed equality for the K-injective normalized canonical comparison. These are the comparisons of the scheme definition, so its hypothesis is fulfilled. The step gives the explicit two-factor square comparison and explains the triple-factor reassociation and inverse cancellation; it does not treat chosen derived functors as literally equal.

Step 3 uses def-pc-derived-base-change-map, whose statement explicitly defines the map as the adjunct of pushforward applied to the horizontal unit and canonical direct-image composition maps. It uses lem-pc-ringed-spaces-derived-adjoint, which states the bifunctorial Hom bijection for all D(O), so forward/inverse cancellation gives the two equations. The first has domain S_fE, the second S_gS_fE. All four arrows have the indicated source and target.

Step 4 uses that same definition and Hom bijection and the natural composition comparison from lem-pc-derived-direct-image-composition. Applying S_m to the pasted map and precomposing with eta_m gives three displayed equalities: the bottom adjunct equation, naturality of the comparison S_mS_g' = S_gS_l at B, and the top adjunct equation. This is a short functorial computation, hence elementary, with the substantive inputs cited. The resulting map is S_gS_f(eta_k), exactly the outer defining adjunct, so injectivity gives the identity with rho and rho' in the original directions. No mate invertibility assertion is used.

I checked identity f, identity g, identity m, zero E and empty schemes: the unit calculation reduces to the corresponding unit/identity law and zero-map identity. For a non-flat base change (Spec F_2 to Spec Z), the proof remains an equality of derived maps and never assumes that a base-change map is an isomorphism. Every step is under 2000 characters (482, 975, 630, 904); no long step hides a separate comparison lemma. No new statement is asserted that needs its own small-case test. B1-B10 are met by reusing existing notions and retaining metadata; C1-C8 were checked against the actual cited statements and declared generic off-unit tool uses; D1-D5 are met by the explicit unit computation; E1-E7 were checked through the domains, comparison directions, and the non-flat case. No SGA source is used.

## Unfinished work

None in this stage-1 split. The existing dependency nodes retain their own states; this delivery does not claim to have proved them in Lean.
