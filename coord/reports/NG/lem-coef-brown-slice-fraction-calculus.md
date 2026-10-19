# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-brown-slice-fraction-calculus.json`: existing item, statement unchanged, split into 15 steps; not a Mathlib match.
- `citations.json`: 15 entries, one for each step/node use, with literal statement excerpts.
- `report.md`: this report. No new DAG nodes; no Mathlib leaves. `write_split.py` is a sandbox-only preparation script, not part of the delivery.

## Attachments

None. Searched the whole read-only `WeilConjectures/` source for the blueprint tag, Brown, fibrant slices and slice fractions. The Brown hits are Brown representability in exceptional-adjoint files, not a theorem about localizing fibrant slices. No exact project declaration exists to attach. The item has no Lean audit entry giving a declaration to inspect.

## Wanted sources

WANTED: Denis-Charles Cisinski, *Higher Categories and Homotopical Algebra*, CatLR.pdf, archival copy of Propositions 7.4.13–7.4.16, Theorem 7.5.18 and Corollary 7.6.13, for lem-coef-brown-slice-fraction-calculus. The URL in the item's source was opened online and these passages were read, but the document is not archived in literature/. No download or literature edit was made.

The proof is marked agent-written. It gives an explicit fraction/Quillen-B argument, rather than presenting the source's approximation/saturation argument as if it were already split. This source has no applicable Stacks tag; none is invented. No SGA source is used.

## What was wrong or incomplete

The existing statement is correct and is preserved, including retract closure, the restriction to fibrations in the ordinary slice, the coherent-functor-category universal property, and the specified section's triangle homotopy. Its proof was empty. The essential comparison must concern mapping spaces, not just Hom sets or an unspecified section in the ordinary homotopy category.

The source's Corollary 7.6.13 states the localization comparison for the whole slice; Theorem 7.5.18 applied to that slice restricts it to its fibrant objects C(b). The new proof establishes this directly, so it neither adds a model-category hypothesis nor assumes saturation of W. The proof also does not use the parent finite-direct-diagram rectification, which would be circular.

No target, coefficient category, base-change morphism, unit realization, chapter or maintainer-owned metadata was changed. The unit is sk-prop-sf-biduality-general. The current main-20261015 proof of prop-coef-integral-exceptional-adjoint was read: the inherited ancestry serves its second-paragraph coefficient-adjunction and inverse-limit calculation through the finite-diagram technical chain. Nothing changes the prescribed route.

## Not duplicates

No new nodes. Existing statements used are the fraction-model theorem, Quillen B for discrete-fibration base change, natural-transformations/nerve homotopy, the join-slice/arrow-slice equivalence, the singleton cone mapping-fiber formula, homotopy-fiber detection, mapping composition, and the full essential-image theorem. Whole-DAG searches for slice/localization and the blueprint_refs searches for slice and fibrant found no blueprint node stating this comparison; the latter returned no fibrant blueprint node. The inherited same_as remains []. The already reviewed Brown pullback theorem contains useful arguments in its proof, but its statement does not assert right properness. Accordingly the split writes those arguments out instead of citing that theorem for a claim absent from its statement (C3/C4).

## Mathlib searches

The sandbox search log records six new real searches: LeanFinder for the coherent Brown slice comparison and for specified-section refinement; Loogle for `"HomotopicalAlgebra", "Over"`; grep for slice/localization/fibrant-over phrases; LeanSearch for localized slice and specified sections; and a second grep for Brown/fibrantObjects/ModelCategory.over. All services responded. Actual query text and returned log records are in mathlib_searches, in addition to the inherited records, without fabricated queries.

Read Mathlib AlgebraicTopology/ModelCategory/Over.lean, especially its description and definitions at 14–25 and 64–109 and ModelCategory.over at 143–145; CofibrantObjectHomotopy.lean at 30–83; and BrownLemma.lean at 13–48. The first constructs ordinary over-category classes/model structures, the second an ordinary quotient, and the third assumes a ModelCategory. None states coherent Brown slice localization under the item's assumptions. The second semantic phrasing found fibrant Brown factorizations with the same model-category hypothesis, not the requested slice equivalence. Thus there is no Mathlib leaf.

## Review by NG

I read coord/delivery-errors.md B–E in full and audited the actual proof against the cited node statements, not their proof text. There are no new statements requiring B's node-creation or Mathlib-leaf checks. The item statement introduces C, W, F, T, slices, coherent sections, and the universal localization itself; its only external definition is def-cbc-enhanced-diagrams-cones, already in stmt_deps. Every proof step has an explicit Boolean elementary flag, proof_deps is the exact union of uses, all cited nodes exist and are unmerged, and citations.json quotes were checked as literal substrings of their statements.

Source reading: online CatLR.pdf, Propositions 7.4.13 (factor the graph), 7.4.15 (base change between fibrant objects), 7.4.16 (right properness), paragraph 7.6.12 (slice structure), Theorem 7.5.18 (fibrant replacement/localization), Corollary 7.6.13 (slice comparison), and its proof were read. The source uses an approximation theorem after saturation; the independently written proof here instead uses two existing generic theorems whose full hypotheses were checked. There is no new node whose source could disguise a restatement of the item.

Steps 1–2 are direct verifications from the stated axioms. The graph exists because all objects are fibrant; its projections are fibrations, and the identity composite implies the denominator is in W by two-out-of-three. If the original arrow is weak, the other projection is weak as well. In the slice, the intermediate structure map is the composite of two fibrations. This is why no object with a nonfibrant structure map was admitted. Retracts remain retracts after forgetting the structure map.

Step 3 uses the statement of lem-coef-trivial-fibration-fraction-model, which explicitly supplies essential surjectivity, the universal property on entire coherent functor categories, and mapping spaces modeled by nerves of fractions. Its split-factorization, pullback-stability, and two-out-of-three hypotheses are all proved or assumed here. Fraction apex maps are arbitrary commuting maps, as that statement requires; restricting them to trivial fibrations would be incorrect. Equivalence with any other specified localization follows from the full universal property in both directions.

Step 4 proves base-change preservation between fibrant objects using the two trivial-fibration projections of a graph and their common section. Step 5 writes the section case of right properness, including the two maps identifying j*E0 with E; I checked both composites using dj=1. Step 6 reduces a general weak equivalence to that section and a trivial fibration, and identifies the iterated pullback projection with the original one. These steps use only already written arguments and pullback/identity/two-out-of-three calculations; they are elementary steps, not new nodes or an uncited use of Ken Brown's lemma.

Step 7 uses lem-coef-infinity-slice-arrow-equivalence to move from the join convention in the item to the fixed-target arrow category, then the exact singleton-shape cone formula of lem-cbc-enhanced-functor-cone-calculus to compute its mapping spaces as homotopy fibers. Lem-coef-spaces-homotopy-fiber-detection permits taking fibers of a total-space equivalence over the identical base. Lem-coef-infinity-mapping-composition identifies invertibility on components with actual equivalence edges. The two inverse equations in the slice are obtained explicitly by surjectivity and injectivity of postcomposition on components. This checks that the statement about inverting weak arrows in the slice is a proved fact, not an unmentioned conservativity theorem.

Step 8 uses the coherent universal-property clause of the fraction-model node, after Step 7 has verified that the ordinary slice functor inverts its weak equivalences. It only constructs G_b, without presuming that it is an equivalence.

Step 9 uses the mapping-space clause of that same fraction-model theorem inside C(x), whose Brown hypotheses were checked in Step 2. I checked the comma isomorphism on objects and arrows: the equations sh=t and ch=rg give the two pullback coordinates, and the equations on an apex arrow are exactly the equations after these projections. The composite y_a to u to x is a fibration because both factors are fibrations.

Step 10 uses the naturality clause of the fraction-model theorem. The transition h has h in W by the two denominator equations. The induced h_y is the pullback along y_a1 to u1, which is a fibration, so Step 6 applies and makes it a genuine W-arrow in C(x). Thus the transition is an equivalence on the localized mapping spaces. This verifies all the comma transition maps, with their direction, before using Quillen B.

Step 11 uses lem-coef-quillen-b-discrete-fibration-base-change exactly as stated. Its V is B_/a_p to B, not the vertex inclusion, which need not be a discrete fibration. I checked the unique backwards lift (a', gamma beta) with prescribed target. Its domain's terminal object gives an identity-to-constant natural transformation; the statement of lem-coef-nerve-natural-homotopy-equivalence contracts its nerve. The strict pullback is the comma category on objects and arrows. The comparison is the natural map of that strict square, so the path to a_p is retained.

Step 12 again uses the full fraction-model statement and homotopy-fiber detection. At a_p the extra arrow h is forced to equal t, leaving exactly pt=rg. In particular the apex is an object of C(b) because pt is a fibration. The isomorphism on morphisms is the same one checked in Step 9. The natural fraction comparisons send this data to the fraction together with its triangle over qb, which identifies the comparison with the mapping-space map of G_b. The source localization is essentially surjective by Step 3, so mapping-space equivalences for its ordinary slice objects suffice for all source objects. No identification of homotopy fibers with strict fibers was assumed.

Step 13 uses the essential-surjectivity and fraction-representation clauses of the existing fraction-model node, then factors the right leg to a fibration. Both displayed triangle arrows in the target slice have underlying equivalences, so Step 7 applies. I checked that an arbitrary target domain z, rather than only qx, is treated. Step 14 uses the precise coherent-quasi-inverse conclusion of lem-coef-infinity-full-essential-image; full faithfulness and the whole essential image have already been proved.

Step 15 applies the fraction-model theorem inside C(P), to the two legitimate objects 1_P and t. A map to 1_P is its structure map s, and being over P forces ta=s. The input is a component of the mapping space in the slice, so the fraction represents the specified section with its triangle homotopy; merely using the ordinary equation t h=1 would not have been enough.

I checked small cases: C terminal, b=1, W the isomorphisms (which forces F to be all arrows from the factorization assumption), and the all-weak-equivalences case with F all arrows and finite limits. The resulting comparisons reduce respectively to the terminal category, the localization itself, the ordinary slice, and a contractible localization. For Kan complexes with weak homotopy equivalences and Kan fibrations, the argument correctly computes the homotopy slice and keeps distinct homotopy classes of section triangles. Empty comma categories are allowed throughout; Quillen B is applied with all transition hypotheses, not by assuming every fiber is inhabited. No counterexample or missing hypothesis was found, and no statement correction was necessary.

The generic off-unit singleton-cone tool is declared in split_report.tool_uses. All other proof nodes have the item's unit. I checked that no dependency of any cited node reaches this item before writing the proof. No node was introduced merely for a Brown axiom verification, a clause of the item, or a previously existing fraction theorem. The report and sandbox are left for an independent second reader; nothing is pushed by this worker.

## Unfinished work

No mathematical step is deferred beyond the cited existing nodes. The archival source is wanted as noted above. Delivery awaits the required second reader.

## Second reading by NG

- Step 1: checked graph factorization, projection types, and two-out-of-three against the item hypotheses; verdict correct and elementary.
- Step 2: checked the terminal slice object, inherited Brown classes, factorization, and retract closure; verdict correct and elementary.
- Step 3: checked every fraction-model hypothesis and the universal-property use against `lem-coef-trivial-fibration-fraction-model`; verdict supported.
- Step 4: checked pullback of the graph factorization and the two-out-of-three argument for the pulled-back section; verdict correct and elementary.
- Step 5: checked the section case of right properness, both pullback coordinates, and the explicit inverse identification; verdict correct and elementary.
- Step 6: checked the arbitrary weak-equivalence factorization, iterated pullback identification, and composition in (W); verdict correct and elementary.
- Step 7: checked join-slice conversion, singleton cone mapping-fiber formula, homotopy-fiber detection, and equivalence-edge criterion against all four cited statements; verdict supported.
- Step 8: checked the induced slice functor and its inversion of slice weak equivalences against the fraction universal property; verdict supported.
- Step 9: checked the comma-category/pullback identification on objects and morphisms and the fibration structure map; verdict supported.
- Step 10: checked transition maps, denominator two-out-of-three, pullback right properness, and naturality of fraction mapping spaces; verdict supported.
- Step 11: checked the discrete-fibration lift, terminal-object contraction, strict pullback, and Quillen-B hypotheses against both cited nodes; verdict supported.
- Step 12: checked the fiber comma category at (a_p), its identification with slice fractions, and the mapping-space comparison; verdict supported.
- Step 13: checked essential-surjectivity fractions, factorization of the right leg, and both equivalence arrows in the coherent slice; verdict supported.
- Step 14: checked full faithfulness plus whole essential image before applying the cited coherent quasi-inverse theorem; verdict supported.
- Step 15: checked the specified section as a slice mapping-space point and the strict equation (ta=s) in the fraction; verdict supported.
- New nodes: none; there were no B1–B7 or Mathlib-leaf records to audit.

No source or statement correction was needed. I verified every citation quote is a literal substring of its cited node statement, searched for duplicate declarations and blueprint statements, and reran the recorded Mathlib searches. The only repair was this second-reading report section; the item JSON and citations remain unchanged.
