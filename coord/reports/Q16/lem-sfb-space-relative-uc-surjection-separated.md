# Worker report

## Files written

dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-uc-surjection-separated.json: statement, split into four steps; Mathlib no match. No new nodes and no Mathlib leaves. citations.json contains a verbatim statement excerpt for every citation of every step. searches.jsonl records five fresh searches with actual results, including two semantic phrasings.

## Attachments

None. Read lean/WeilConjectures/AlgebraicGeometry/IsSeparatedOfSurjectiveUniversallyClosed.lean, theorem AlgebraicGeometry.isSeparated_of_surjective_universallyClosed, line 48: its three objects are schemes, so it does not give the algebraic-space statement. Searches of the project for the item's tag and for the geometric notion found no exact declaration.

## WANTED

None.

## Corrections and provenance

The mathematical statement agrees with Stacks 05Z2(4), spaces-morphisms.tex, lemma-image-universally-closed-separated: the base B is an arbitrary algebraic space, a is point-surjective and universally closed, and only U over B is assumed separated. No semantic statement correction was needed; replaced the malformed prime typography V\prime by V^{\prime}. The imported node had no proof. Its inherited blueprint.from.node was null, and blueprint_refs.py ancestor consequently printed None. Following created.item terminates at a Lean module name, Sheaf.SixFunctors.CtfStabilityDirectImages, rather than at a node. The inherited from.place explicitly identifies det-thm-sf-ctf-stability-direct-images proof (3); I filled from.node with that existing blueprint node, preserving the complete place and via list. Read the newest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its sk-thm-sf-ctf-stability-direct-images.proof.md; this is a supporting geometric lemma below that route, not a replacement for a unit step. No unit or chapter was changed.

## Not duplicates

No new nodes. The existing lem-sfb-space-uc-surjection-separation gives absolute separatedness only (05Z2(1),(2)); applying it here would require separatedness of U absolutely, which is not assumed. The scheme theorem lem-weil-pbc-surjective-universally-closed-separated has only scheme objects. Reused lem-sfb-space-separated-diagonal-closed, which is a diagonal criterion, not a descent theorem. Searched all dag/nodes by 05Z2, 03HK, 04XV, 04Y0 and geometric keywords, and ran blueprint_refs.py searches for universally closed, diagonal and separatedness. None of the blueprint hits states this relative algebraic-space descent assertion.

## Unfinished work

None for this one-level split. No new pending statements were introduced.

## Review by Q16

I read the full proof of Stacks 05Z2 in spaces-morphisms.tex and its final diagonal recognition in 04Y0, lemma-separated-diagonal-proper. I also read spaces-properties.tex 03H4, lemma-points-cartesian, and 03BX, lemma-topology-points. There are no new nodes whose sources require separate review. I checked the existing statements of all four cited nodes, rather than relying on their titles or their proofs.

Step 1 uses lem-trf-space-fibre-products-etale-covers for algebraic-space sheaf fibre products and their universal property; def-sfb-space-morphism-properties defines universal closedness for every algebraic-space base change. The two product-map factors really are base changes of a, and the commuting diagonal square follows by its two projections. Stability under base change and composition is proved from the definition by the closed-image argument, not quoted as an uncited theorem.

Step 2 uses the exact iff assertion of lem-sfb-space-separated-diagonal-closed: a morphism of spaces over any scheme S is separated precisely when its relative diagonal is universally closed. In that node the letter B denotes the ambient scheme, not the target; its target V is an arbitrary algebraic space. Thus its use for p:U to B does not assume that the present B is a scheme or separated. The composition argument from step 1 and the universal-closedness definition then apply.

Step 3 uses the sheaf fibre-product node for the two pullbacks, with the mutually inverse sectionwise maps written out. lem-a1-space-point-open-calculus states surjectivity onto the set-theoretic fibre product for arbitrary space maps, so it proves surjectivity of the base change of a without representability or flatness. The very same statement supplies continuity. The inverse-image and image calculation for each closed subset E is written explicitly; this is elementary set reasoning from those cited assertions. Testing every algebraic-space T is exactly the definition of universal closedness, not merely closedness of the diagonal's image. No hidden comparison lemma is being moved into a long step: each step is under 2000 characters and the whole proof is under 3000.

Step 4 uses the reverse implication of the same exact diagonal criterion for q. It already includes representability and closed-immersion recognition, so there is no unsupported appeal to an immersion criterion for arbitrary algebraic spaces. All these citations have verbatim excerpts in citations.json. The off-unit point calculus is declared as a generic tool in split_report.tool_uses; no unit node provides this point-space assertion.

I tested the argument with a the identity, with an empty target, and with a nonseparated base B and U=V=B over B: it never replaces a relative diagonal by an absolute one. If U is empty, surjectivity forces V empty and the closed-set calculation remains valid. Non-Noetherian schemes and closed immersions with infinitely generated ideals introduce no extra requirement, since no finite-presentation result is invoked. There is no quasi-compactness, finite-type, flatness or separatedness-of-base hypothesis hidden in any use. Sections B through E of delivery-errors were checked against the files: no statement-only node is disguised as a proof, no new duplicate or clause node is introduced, all non-elementary facts are existing statements, the pullback objects are the correct ones, and no source error or route change is needed. Mathlib's relevant Separated.lean and UniversallyClosed.lean sources were inspected: all candidate declarations are for Scheme, including UniversallyClosed.of_comp_surjective, so they cannot make this algebraic-space item a leaf.
