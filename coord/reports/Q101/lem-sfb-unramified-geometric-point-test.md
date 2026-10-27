# Q101: lem-sfb-unramified-geometric-point-test

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-unramified-geometric-point-test.json: statement, split; no Mathlib match. Four proof steps, 1959 characters in total, with all statement dependencies and the statement unchanged.
- citations.json: verbatim statements backing every citation in all four steps.
- searches.jsonl: actual searches from the prescribed msearch.py command, retained as provenance.

No new nodes and no new Mathlib leaves. The sandbox started without an item copy, proof or report.

## Attachments

None. Searches under lean/WeilConjectures/ for the exact blueprint tag and geometric-unramified concepts found no declaration proving this entire item. The related Mathlib extension and curve files concern formal unramifiedness or ring loci, not this test with its explicit lifting clause. The parent's theorem is not this statement and is not an attachment.

## WANTED

None. All sources needed for the split are present.

## Findings and changes

The item was a true statement-only child of the reviewed re-split of lem-sfb-geometric-tangent-unramified. There is no statement dispute, no added hypothesis, and no change to the unit route. The missing argument is supplied explicitly: choose an algebraic closure of the residue field of each source point, form its field-valued point and the fibre-product section, reflect membership in the unramified locus, and use the resulting source cover.

I read the current main-20261015 unit and its direct-images proof (3), the recorded chapter/unit JSON and the parent split. The unit JSON carries the older sec-six-functors description, whereas the node and current blueprint place this subsidiary alteration rigidity input in sec-six-functors-basics. I preserve those inherited records rather than edit the unit. The ancestor command returns None; the inherited null ancestor, exact place and full via chain are retained. Whole-blueprint searches for unramified, 0475 and 01J9 found no statement to substitute. DAG searches found the precise existing locus lemma and field-valued-point description, so creating duplicates would be wrong.

Mathlib searches were run with leanfinder (two different phrasings), leansearch, loogle and grep. All five calls succeeded. I read the hits and Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean, including the base-change instance and open-diagonal theorem. They give formal unramifiedness and its stability, not the whole geometric test or the identification of its rational-point tests with the locus of the original morphism. The existing item's older search records are retained as history; only this sandbox's actual new calls were appended. The wrapper log records the exact queries and results.

## Tool use

lem-trf-unramified-locus-base-change is a generic theorem about arbitrary base change of the unramified locus. Its statement, not its proof, is used in Steps 2 and 3. It is the exact input already used by the parent before the re-split and supplies no alternative to any unit-level route. This off-unit use is declared in split_report.tool_uses. Other proof dependencies are Mathlib leaves.

## Not duplicates

No new nodes were created. The item is not a restatement of lem-trf-unramified-locus-base-change: that theorem identifies loci for arbitrary base changes, while the item constructs enough rational geometric-fibre sections and uses them to test the whole morphism. The ordinary and geometric fibre criteria in sec-trace-formula test entire fibre schemes; they do not state this rational-point test with lifting using an algebraic closure of each source residue field.

## Review by Q101

I checked the proof against literature/stacks-project/morphisms.tex Tag 0475, label lemma-set-points-where-fibres-unramified, in full, and schemes.tex Tag 01J9, label lemma-characterize-points, including the preceding pairs description. Tag 0475 assumes only local finite type and explicitly permits arbitrary base change. I also read morphisms.tex definition-unramified (02G4), lemma-unramified-characterize (02G6) and the existing definition node's 02GE equivalence. There are no new-node sources to review.

Step 1 uses def-weil-algebraic-closure, whose statement explicitly asserts existence for every field, and lem-weil-pbc-morphism-from-spec-field, whose statement explicitly gives a morphism from a pair (point, residue-field map) with the specified image. No naturality theorem is implicitly needed: I define s to be f composed with a. def-weil-geometric-point allows every algebraically closed field, and def-pc-fibre-product explicitly supplies the map (a,id) and both projection equations. These facts prove the section and image assertions in a few lines; they are not hidden as a new lifting lemma. I verified the types: both entries have domain Spec Omega, and f composed with a equals s composed with id.

Step 2 cites lem-weil-pbc-lft-base-change to check that each geometric fibre structure morphism is locally of finite type. I opened lem-trf-unramified-locus-base-change and checked that it states W_{h'}=(g')^{-1}(W_h) for any base change and defines W as the union of open unramified source neighbourhoods. Thus the step takes exactly what that statement supplies. For the forward implication X itself belongs to the union when f is unramified, so every fibre point, in particular every test-section image, is in its unramified locus. No flatness, presentation, finite type over a field, or Noetherian condition was used.

Step 3 uses the same equality for the actual point y constructed in Step 1, not an unspecified point of the ordinary fibre. The hypothesis is exactly unramifiedness of p_s on an open neighbourhood of y, so it puts y in W_{p_s}. Taking the inverse image equality back gives z in W_f, for every z. This does not replace a local statement at a point with a global fibre assertion.

Step 4 unpacks the affine-cover formulation explicitly included in def-weil-unramified-morphism's parenthetical equivalence with Stacks 02G4. Each unramified source neighbourhood supplies its affine unramified charts; their union covers X and retains the same ring maps. This is a covering argument of a few lines, so I kept it as an elementary step rather than invent a source-locality node. For empty X the empty covering gives the same conclusion. Every citation's full statement is copied verbatim into citations.json and is long enough to show its content.

Small cases checked: empty X (both tests and lifting are vacuous); an identity morphism (its geometric fibres are points); a generic point of A^1 over k (the chosen Omega is an algebraic closure of k(t), showing why extensions transcendental over the base point's residue field must be allowed); A^1 over an algebraically closed field (its rational fibre point has no unramified neighbourhood, so the test fails as it should); the dual-number scheme over that field (the test fails at its unique point); and the finite purely inseparable extension F_p(t^{1/p}) over F_p(t) (its geometric fibre is nonreduced, so the test does not incorrectly accept it). All these use the same field-valued section construction and require no separability in the point lift.

I checked delivery-errors B through E point by point: no new node or unsearched leaf, no undefined auxiliary object, no proof hidden in a new statement, no non-elementary tag without its cited node, no use of a cited node's internal proof, no whole-item transfer, and no direction requiring a stronger hypothesis. The only non-elementary steps are the two explicit applications of the existing locus theorem; every step is below 2000 characters. The locality and universal-property arguments are written out. No SGA source or Lean/compiler/build tool is used. Dependency traversal finds no path from any cited node back to this item.

## Unfinished work

None in the mathematical split. Required dry-run and push results are recorded below when available.

## Validation

The prescribed deliver.py --no-push invocation completed successfully: OK (not pushed) at d3ade1b4c6e, server preflight passed. The local read-only dependency traversal checked 81 existing nodes without a return path to this item, and every quotation in citations.json was verified verbatim. No mathematical or preflight repair was required.

## Repair of the live-promotion return (2026-10-23)

The return has one point: the previous reader-approved completion existed only in the side DAG, while the live queue still saw an unsplit item. I continued the retained sandbox rather than discarding its four-step proof, report, citations or five logged searches. The initial required dry run exited successfully at 14a6756f7f5, which rebuilt the delivery on the server's current DAG. I then rebuilt the sandbox item from the current live JSON, applying only the retained stage-1-owned fields. The live statement and all seven statement dependencies are identical to the retained version; live has status unsplit, no reviewed record and no Lean attachment. There is no released repair note for the item. This repair does not claim that a side completion has already been promoted: the new delivery is for L to land in the live DAG.

I re-read every current proof citation: def-weil-algebraic-closure supplies existence of the chosen field; lem-weil-pbc-morphism-from-spec-field supplies the pair-to-morphism construction and its image; def-weil-geometric-point permits this algebraically closed field without algebraicity over the base residue field; def-pc-fibre-product supplies both projection identities; lem-weil-pbc-lft-base-change supplies local finite type for every p_s; lem-trf-unramified-locus-base-change states precisely the inverse-image equality for arbitrary base change; and def-weil-unramified-morphism includes the affine-chart characterization used to assemble the source cover. All eight retained quotation entries remain verbatim in these current statements. Thus no changed dependency statement requires a replacement citation. I also read the current statement definitions of schemes, finite type and residue fields and the current reviewed parent split, which still delegates exactly old Steps 3--5 to this item.

The source re-reading was morphisms.tex label lemma-set-points-where-fibres-unramified (0475), the full locally finite type assertion and its arbitrary-base-change clause; label lemma-base-change-finite-type (01T4); definition-unramified (02G4) and lemma-unramified-characterize (02G6); and schemes.tex the discussion of pairs preceding lemma-characterize-points (01J9) and definition-fibre-product (01JP). In Step 1 the algebraic closure is of kappa(z), so the lift exists for generic as well as closed source points. In Steps 2--3 the only hypothesis of the locus theorem is local finite type, checked for f in the item and p_s by the cited base-change lemma. I made a concrete clarification in Step 2 that this equality is established independently of f being unramified, and Step 3 now explicitly reuses that previously checked local finite type hypothesis. This removes any possible scope ambiguity in applying the converse. Step 4 still uses the unchanged affine-chart definition, including the empty cover when X is empty.

I rechecked the edge cases from the original review: the empty source, identity, generic point with transcendental residue extension, affine line, dual numbers and a purely inseparable field extension. The same test behaves correctly in each case. No hidden lemma was introduced: all four steps remain below 2000 characters and the whole assembly below 3000. The current main-20261015 unit and direct-image proof (3) and inherited ancestor chain are retained. The Mathlib search questions and statement have not changed, so the five actual logged search results were read and reused, not rerun or invented. No new node or Mathlib leaf is introduced. This section supplements my signed Review by Q101 above and discharges the single return point by a current-DAG delivery, rather than an unchanged re-push.
