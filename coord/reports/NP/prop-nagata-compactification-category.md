## Worker report

Files written:
- dag/nodes/sec-nagata-compactification/prop-nagata-compactification-category.json: statement, split using existing nodes; no Mathlib match for the whole statement.
- dag/units/sk-prop-nagata-sketch-comp-category.json: only realized and realized_by; all three unit steps are carried by the item.
- citations.json: full verbatim statements for every step citation.

New nodes: none. Mathlib leaves created: none.

Attachments: none submitted. Project declarations in Compactification/Cofiltered.lean, CommonRefinement.lean, CategoryBaseChange.lean, BaseChange.lean and NagataCompactification.lean cover the positive assertions (including the constructed graph image and comparison projections). I read their signatures and proofs; the census comments indicate standard axioms for the major assertions. The arbitrary-base-change failure of density is only prose there, not a proved declaration located by the searches, so I did not claim an attachment for every clause of this item. No upstream master sorry is treated as a proof.

WANTED: none.

The imported proof left the equalizer step elementary=null and uncited. It also invoked proper stability, graph closedness and open-immersion stability without the nodes stating them. The flat comparison cited lemma-nagata-dense-flat-pullback for a general image comparison that is in its proof but not its statement. I repaired this using its actual density statement, then an elementary affine ideal argument. The finite-family proof now explicitly includes the empty and singleton cases. No unit route is replaced: the equalizer closed subscheme, rather than the different dense-refinement uniqueness proof in Lean, still proves (ii).

## Statement dispute in a dependency

STATEMENT-DISPUTED: def-nagata-scheme-theoretic-image says "largest closed subscheme"; Stacks morphisms.tex definition-scheme-theoretic-image (Tag 01R7; existence Lemma 01R6) says smallest. The identity closed subscheme Y is always the largest through which any map to Y factors; for D(t)→Spec K[t] disjoint-union Spec K (map into the first component), that would incorrectly give the entire disjoint union, including the second component. The kernel description in the same dependency instead excludes that component. I cannot edit another worker's node. The item's statement therefore now explicitly specifies the smallest closed subscheme for its quasi-compact graph map, with the kernel description; its proof uses the correctly oriented lemma-nagata-scheme-image-universal. This repairs the item's meaning faithfully to the source, without silently importing the erroneous word. There is also a non-quasi-compact caveat in that dependency's general kernel formula (Stacks 01R8); all maps whose images are used here are quasi-compact, so it causes no gap here. The mathematical conclusions of the item are unchanged.

Unfinished work: none in this one-level split. The dependency definition correction is reported for its owner; this delivery does not change it.

## Not duplicates

No new node was created. DAG searches for graph/closed immersion, proper stability, quasi-compact base change, flat base change, and compactification/cofilteredness found the existing statements used here. The whole-blueprint search for "compactification category" found this item and narrower or differently purposed finite-field statements, not an identical statement including both the arbitrary-base comparison and density warning. Searches of project Lean by the item id and compactification notion were read before splitting. All Mathlib queries in the node are actual msearch.py calls; LeanSearch returned Internal Server Error and is recorded unavailable, Loogle reports unknown identifier AlgebraicGeometry.Compactification, the AlgebraicGeometry grep found no compactification, and two LeanFinder phrasings returned affine transition-limit results, not this theorem.

## Review by NP

I read the master's node source and its unit and chapter records, then the actual Stacks text: schemes.tex definition-separated (01KK) and lemma-base-change-immersion (01JY); morphisms.tex lemma-composition-proper (01W3), lemma-base-change-proper (01W4), lemma-closed-immersion-proper (01W5), lemma-factor-quasi-compact-immersion (01QV), lemma-scheme-theoretic-image and definition-scheme-theoretic-image, lemma-quasi-compact-scheme-theoretic-image (01R8), lemma-scheme-theoretically-dense-quasi-compact (01RD), lemma-characterize-scheme-theoretically-dense (01RE), lemma-base-change-flat (01U9), and lemma-flat-base-change-scheme-theoretic-image (081I). There are no new node statements to check. The whole proof is marked agent-origin because it repairs the blueprint argument using these geometric tools and elementary universal-property arguments.

Step 1 reads exactly the properness clauses of closed-immersion-proper, proper-composition and proper-to-separated-target; the proper definition supplies separatedness. Identity and equation checks are elementary. Step 2 uses the final sentence of thm-nagata-compactification under precisely qcqs S and separated finite-type f, and the compactification definition supplies quasi-compactness of its open immersion.

Step 3 cites proper-base-change and proper-composition for Y→S. The graph is a pullback of the separated diagonal, whose closedness comes from the proper definition; closed-immersion-base-change supplies its closedness. Open-immersion-base-change supplies the second factor, and the definition of immersion states this closed-then-open order. I read finite-type-to-separated-target: it applies to X→Y→S since f is finite type and Y→S has just been proved proper/separated. Its finite-type conclusion supplies quasi-compactness by the finite-type definition. No cancellation claim about immersions is used without proof.

Step 4 uses the immersion-construction definition together with immersion-into-proper, and uses immersion-open-in-scheme-image for both quasi-compactness and scheme-theoretic density. The image-universal statement gives the factorization equality, and proper-to-separated-target gives proper projections with the established proper source and separated targets. Step 5 is elementary finite induction with an explicit empty-family object, singleton identity, and composite arrows.

Step 6 opens every cited statement: separated means a closed diagonal; closed-immersion-base-change gives the equalizer inclusion; closed-immersion-proper gives both its properness and properness over S. Fibre-product universality gives j_E. The displayed test-object argument proves the square cartesian, using only the monomorphism cancellation that follows from closed immersion's quotient description. Open-immersion-base-change then gives openness, and open-immersion-qc-over-separated-target applies with X→S finite type and E→S separated. Thus factoring j_1 is not mistaken for merely containing its set-theoretic image. Step 7 just spells out the definition of cofilteredness; no small indexing-category existence theorem is being invoked.

Step 8 uses compactification-base-change exactly for objects and proper-base-change exactly for arrows; fibre-product universality supplies all equations and functor laws. It never assumes qcqs of S′. Step 9 uses the image-universal statement, which really includes a closed immersion into any closed factorization, and closed-immersion-base-change for that factorization after pullback. Projection equations and compatibility on X′ follow by monomorphism cancellation and the fibre-product equations. The separated-finite-type-base-change statement checks that the graph construction continues to apply over the unrestricted S′.

Step 10 no longer takes flat image commutation from the proof of a density lemma. Flat-morphism-base-change supplies the flat projection; dense-flat-pullback is applied only to the quasi-compact quasi-separated dense open j. Quasi-separatedness follows directly because an open immersion is a monomorphism and its diagonal is an isomorphism. The remaining argument is written on Spec A with closed subscheme Spec(A/I): density forces I=0. This is elementary from the cited density and closed-immersion descriptions, and is why this step is marked elementary despite its named inputs. Step 11 checks the same hypotheses for an arbitrary dense c and supplies the counterexample by K[t,t⁻¹] tensor K=0. In particular its failure is schematic (K→0), not just a set-theoretic density argument.

Small cases checked: X empty (empty graph image, equalizer still contains the empty open), empty and singleton finite families, g identity (comparison ideal zero), flat field extensions, and the nonflat closed point t=0 (nonempty ambient and empty source). No reducedness, noetherianness, density of arbitrary objects, flatness of arbitrary g, finite presentation, or qcqs of S′ is introduced. Corrections made during this review were the missing geometric citations, the explicit equalizer cartesian test, the finite-family base cases, the density-only flat comparison, and the inline correction of the image definition's reversed extremum. Generic geometric inputs from other units are declared as tool uses where necessary; they do not replace any unit step.

## Second reading by NP

- Item statement: checked against the blueprint node and Stacks Tags 01KK, 01JY, 01W3–01W5, 01QV, 01R6–01RE, 01U9, and 081I; hypotheses and clauses agree, including the non-flat density caveat and smallest-image convention.
- Step 1: checked proper identity, composition, and proper-to-separated-target statements; equations and category laws are elementary, and cited nodes supply the geometric inputs.
- Step 2: checked Nagata's qcqs/separated finite-type hypotheses and the compactification definition; the empty source is included.
- Step 3: checked the graph pullback, diagonal closedness, immersion factorization, properness, and finite-type hypotheses against the cited nodes; no unstated base hypothesis is used.
- Step 4: checked immersion compactification, open dense image, image universal property, and proper projections; each cited statement supplies the fact used.
- Step 5: checked finite-family induction with empty and singleton bases and composition of refinements; elementary as written.
- Step 6: checked the equalizer pullback, closed/proper base change, cartesian test, open immersion, and quasi-compactness hypotheses; monomorphism cancellation is explicitly justified.
- Step 7: checked the cofilteredness definition and its application to Steps 2, 4, and 6; elementary.
- Step 8: checked arbitrary base change of objects and arrows, proper base change, fibre-product functor laws, and the absence of a qcqs hypothesis on the new base.
- Step 9: checked the comparison closed immersion through the image universal property, refinement equations, and separated finite-type base change; all uses match the cited statements.
- Step 10: checked flatness, quasi-compact/quasi-separated density hypotheses, and the affine ideal argument for the comparison isomorphism; no proof-only image-commutation claim is used.
- Step 11: checked the localization/quotient counterexample and flat density preservation; no assertion of failure for every non-flat map is made.
- New nodes: none; no new-node B1–B7 or duplicate repair is needed. Existing dependency citations have verbatim statements in citations.json.
- Small cases: empty source, empty and singleton finite families, identity base change, flat field extensions, and the non-flat closed point were checked.
- Changes: added this second-reading record, made Step 10 explicitly derive sheaf injectivity from the density lemma’s image conclusion using the quasi-compact kernel description, and treated the empty principal open separately in Step 11. The dependency's reversed largest-image wording remains explicitly STATEMENT-DISPUTED; the item's smallest-image convention and the worker's repairs are retained.
