# Worker report: lem-sfb-space-thickening-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-thickening-base-change.json: statement, split; no Mathlib match for algebraic spaces. Four proof steps, all below 2000 characters. Added explicit dependencies for the point classes and atlas topology already used in the statement.
- citations.json: eight entries, one for every step/node pair; each quote is copied verbatim from that node's current statement.
- searches.jsonl: actual msearch.py searches; the item retains the inherited Q89 searches and appends the five searches run here. No earlier sandbox attempt existed.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched all of lean/WeilConjectures for the blueprint tag, algebraic-space wording, and thickening/space concepts. The thickening declarations concern schemes, including first-order thickenings. No project declaration states every clause for algebraic spaces. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are present in literature/stacks-project.

## Corrections and scope

The imported assertion is true as stated, with no finite-order assumption. Its proof was empty. I retained its statement and inherited provenance, adding links to the existing point-class and topology definitions; no mathematical hypothesis or conclusion changed. Stacks Tag 09ZX has an omitted proof, so proof_origin is agent, with an explicit reconstruction from the supporting sources rather than a claim to have read a proof which is not there.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and the chapter and unit records were read. The inherited provenance through nodal curves and Tag 09ZY is a supporting geometry input to the recorded direct-image route; no unit or chapter route is replaced. blueprint_refs.py ancestor reports None for this existing created-item chain; I retained that existing value and its detailed from.place and via list. Blueprint searches for thickening, closed immersion and point topology found no blueprint assertion equal to this item; same_as remains []. No repair note exists for this item.

The generic algebraic-space fibre-product node is declared in split_report.tool_uses. The two scheme results used below are existing Mathlib leaves, and the finite-space topology node is in the item's unit. Their use introduces no route through the trace formula or purity: the cited statements are foundational fibre-product, scheme-immersion and topology facts. In particular there is no SGA source.

## Not duplicates

No new node was created. The existing scheme closed-immersion/finiteness/monomorphism nodes are used directly. The existing lem-sfb-finite-space-morphism-topology supplies exactly continuity and closedness, rather than creating a second closed-immersion topology lemma. The parent lem-sfb-space-thickening-topological-properties is not cited, so the split does not circle through its consumer.

## Review by Q93

I read spaces-more-morphisms.tex, lemma-base-change-thickening (09ZX), and verified that its first clause covers arbitrary thickenings, while its extra first/finite-order clause is separate and unnecessary here. I also read spaces-morphisms.tex, lemma-immersions-monomorphisms (042R), etale.tex, lemma-characterize-closed-immersion (04XV), spaces-properties.tex, definition-points (03BU), lemma-points-cartesian (03H4), and lemma-topology-points (03BX), plus the closed-immersion finite lemmas in morphisms.tex (035C) and spaces-morphisms.tex (081Y), and the integral/universally-closed lemma (0415). There are no new nodes requiring further source reviews.

For step 1, I opened def-trf-algebraic-space and lem-pc-proper-monomorphism-closed and read their statements. The former says that algebraic spaces are sheaves, maps are natural transformations, and a representable scheme test is a scheme. The latter explicitly says closed immersion if and only if proper and monomorphism for schemes, so its forward direction really does give the scheme cancellation used. The scheme test P exists because the closed immersion is representable. Equality of two sections follows by cancelling P -> R; equality of transformations then follows component by component. This proves the stronger intermediate fact for any representable closed immersion, which is applied again to the base-changed map. It is a short argument from the cited statements, not an uncited immersion theorem or a new node restating a clause.

For step 2, I opened lem-trf-space-fibre-products-etale-covers and def-trf-algebraic-space again. The former explicitly supplies sheaf fibre products in algebraic spaces, with their universal property. Representability of P -> T and the scheme closed-immersion test follow directly from (Z times_W T) times_T R = Z times_W R. I wrote the section-level correspondence, so no unstated base-change permanence theorem is being imported. The test R -> W is the composite through T, which is allowed for every scheme R by the original closed-immersion hypothesis. T itself need not be a scheme.

For step 3, I read def-a1-algebraic-space-point-classes and the fibre-product node. The first explicitly defines equality after a common field extension, and the second gives the sheaf fibre product; their statements suffice for both constructed pairs. Surjectivity uses only the surjectivity part of the original homeomorphism. For injectivity I extend two representatives until their images agree in T and then use the scheme-section injectivity already proved for p. No residual-field identity or topological fibre-product identity is assumed. This expands precisely the common-field argument of 03H4, and it is elementary from those definitions and the earlier steps.

For step 4, I opened lem-weil-pbc-closed-immersion-finite and lem-sfb-finite-space-morphism-topology and checked their full statements. The former concerns schemes; it is applied only to the represented scheme tests from step 2. The latter assumes exactly finiteness on every scheme test, with no finite-presentation, Noetherian or separatedness hypothesis on the ambient spaces. It explicitly concludes continuity and closedness for the point spaces with the atlas topology, which is the full topological input used. I checked that its dependencies do not return to this item or its thickening-topology parent. Closed bijective continuity then gives a continuous inverse by testing closed sets. Step 4 is marked non-elementary because it invokes this space topology theorem; the final inverse-map check is written out.

I checked B--E against the actual files: no unsplit new proof, no new definition, no new Mathlib leaf, no hidden external theorem, no new node equivalent to the item, and no circular invocation of the parent. All citations use statements, not proofs of nodes. The whole proof has step lengths 847, 617, 850 and 606 characters, so none is a long step concealing another claim. The item Mathlib searches were actually run with two distinct semantic phrasings, Loogle, grep and LeanSearch; all services returned answers. The hits are schemes or ring-theoretic base change and do not specialize to algebraic spaces in one line. I read Mathlib's IsClosedImmersion.iff_isProper_and_mono at ZariskisMainTheorem.lean:393 and IsClosedImmersion.iff_isFinite_and_mono at Morphisms/Finite.lean:124 to confirm the existing leaf statements used, and did not claim an algebraic-space match.

Edge cases checked: the identity thickening; an empty target (all spaces and tests empty); an empty base change of a nonempty thickening; arbitrary non-reduced T; and a non-finite-order thickening Spec(k) -> Spec(k[x_1,x_2,...]/(x_n^(n+1): n>=1)), whose ideal generated by the x_n is nil but has no uniform nilpotence bound. The proof still applies, since every scheme test of a closed immersion is finite even when its defining ideal is not finitely generated. A non-surjective closed immersion would satisfy cancellation and closedness but fails exactly the lifting step, so the homeomorphism hypothesis is used in the correct place. No flatness or finiteness of the base-change map was added.

## Unfinished work

None in this one-level split. The required dry run and push are performed after writing this report; their output determines the final delivery disposition.
