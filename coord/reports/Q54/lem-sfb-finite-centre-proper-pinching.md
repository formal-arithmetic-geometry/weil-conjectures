# Q54 stage-1 report: lem-sfb-finite-centre-proper-pinching

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-centre-proper-pinching.json: statement item split into eight steps. Statement and statement dependencies retained; no new nodes, no Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the 21 step/node citation pairs.
- searches.jsonl: actual msearch command log, retained unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint docstring tag, item id, pinching, Pinch and Ferrand. No declaration was found. The Mathlib hits do not give the item: Pullbacks.isPullback_SpecMap_of_isPushout sends a ring pushout to a scheme pullback, whereas the required construction sends a surjective-leg ring fibre product to a scheme pushout. Morphisms.Affine.isPushout_appTop_of_isPullback goes in the other algebraic direction as well. Proj properness and integral base-change instances supply only familiar inputs.

## WANTED

None. All source arguments are present in literature/stacks-project.

## Issues found

The original node was statement-only. Its statement is correct, including centres containing nonclosed points. In particular, it would be incorrect to replace its finite underlying-set hypothesis by an assertion that every finite scheme over an arbitrary Noetherian ring has a finite underlying set. No such assertion is used. Finite Z/S is an additional hypothesis, distinct from finiteness of |Z|.

The existing general lem-sfb-ferrand-scheme-pushout already gives the pushout, integral map, closed immersion, cartesian square, sheaf description, compatible affine charts, complements, open restriction, separatedness and local finite type. It was reused rather than duplicated. Its statement gives only integrality of a, so the finiteness assertion required the explicit module calculation in steps 5--6. In that calculation the coefficients e_k in E must be lifted through A -> D after applying E -> D: E does not act on A directly. The proof writes those lifts r_k and the coefficients (r_k,e_k) in the fibre-product ring, and includes the kernel remainder (h,0). This checks the potentially misleading short sentence in the source's 00IT proof.

The item has blueprint.from.node = null through its existing created-node ancestry. The prescribed ancestor command returns None. That inherited field is retained rather than inventing an imported ancestor. The precise existing from.place is already filled and retained. Read the current latest direct-image proof clause (3), which now states compactification and preservation, rather than the obsolete literal alteration wording in this historical ancestry. This split works below that route and changes no chapter or unit.

## Not duplicates

No new nodes. Reused lem-sfb-ferrand-scheme-pushout (0E25/0E26/0E27), lem-sc-ample-finite-set-affine (01ZY), lem-weil-pbc-projective-ample-invertible, lem-kun-projective-implies-proper, pqf-lem-finite-integral-lft, lem-weil-pbc-finite-proper, lem-weil-pbc-image-universally-closed, pqf-lem-lft-fp-locnoeth and lem-pc-separated-quasi-separated. Also inspected the affine-only and compatible-affine pinching nodes and the relative nodal pinching node. None needs a new wrapper. Whole-DAG searches by Stacks tags, titles and statement keywords and tools/blueprint_refs.py searches for pinching, 0E25 and proper pinching found no exact blueprint duplicate of the item.

## Review by Q54

I read Stacks more-morphisms.tex, Situation pushout-along-closed-immersion-and-integral, Proposition 0E25 and its entire construction, Lemmas 0E26 and 0E27; more-algebra.tex Lemma 00IT and its generator argument; properties.tex Lemmas 01ZY and 01PU; morphisms.tex the locally-projective-proper argument (01WC), the proper-image lemma 03GN and the Noetherian finite-type finite-presentation lemma (01TX). These support the proof as written. There are no new nodes whose sources need a separate review.

Step 1 uses def-kun-projective to choose a finite projective-space embedding, lem-kun-projective-implies-proper for properness and lem-weil-pbc-projective-ample-invertible for absolute ampleness. I opened their statements: the embedding convention is exactly finite H-projectivity, and the ample lemma assumes an affine base, as supplied here. Step 2 uses the full finite-set lemma, which has no closed-point assumption, and pqf-lem-finite-integral-lft for j's integrality. This verifies all three hypotheses of the general Ferrand statement.

Step 3 uses only the explicit assertions of lem-sfb-ferrand-scheme-pushout. Its affine chart, structure-sheaf, cartesian, open-restriction and all-schemes universal property clauses are actually in its statement, not merely in its proof. Step 4 uses its quotient topology and complement isomorphism, together with the definition of surjectivity. Every point of T is hit by j and hence b(T) is contained in a(X); this proves a's surjectivity and removes the extra T-complement summand without adding a nonempty hypothesis.

Step 5 uses that same statement's affine and open-restriction assertions on an arbitrary affine W in P, plus the actual affine clause of lem-weil-pbc-closed-immersion-integral-separated-uc. The inverse images in T and Z are affine because b is closed affine and j finite affine. Applying the existing affine-case pushout assertion after open restriction gives W = Spec(A times_D E) even for an arbitrary affine W. The definition node def-weil-finite-integral-morphism gives finite generation of D over E. Step 6 proves finite generation of A over B directly, with every coefficient and remainder exhibited. This is elementary module algebra, not a new lemma or an unproved application of 00IT. Checking every affine W makes finiteness follow directly from the definition and avoids using an uncited locality theorem.

Step 7 uses pqf-def-locnoeth with the single affine S and its Noetherian coordinate ring. It uses the exact finite-implies-proper statement lem-weil-pbc-finite-proper for T and Z, and the definition of properness to supply separatedness and local finite type. Thus both hypotheses in the separatedness/local-finite-type clauses of the general Ferrand node are satisfied. The exact proper-image node lem-weil-pbc-image-universally-closed assumes a surjection and a universally closed source, both already proved; its final clause supplies properness because P has the other two properties. Step 8 uses pqf-lem-lft-fp-locnoeth with the locally Noetherian base just verified, properness for quasi-compactness, and the exact separated-implies-quasi-separated node. These meet all three defining conditions for finite presentation in def-sbc-locally-finite-presentation.

I checked empty Z,T, empty X and the zero base ring. If Z is empty, surjectivity of j forces T empty, so the square reduces to P = X. If X is empty, Z and T must also be empty. The empty scheme is affine Spec(0), and the module argument permits the zero ring and no generators for D=0. The identity pinching (j an isomorphism) reduces to P = X; the case i an isomorphism reduces to P = T and the same generator calculation is ordinary finiteness of j. No flatness, smoothness, degree, fibre-dimension, or closed-point condition enters any step. None of the steps exceeds 2000 characters. No statement correction or forbidden SGA source was needed.

For B--E I checked self-containedness and retained every definition dependency of the original statement; copied literal quotations from the cited statements; checked that no source tag substitutes for a missing node; avoided any new node that restates a clause, is elementary, or duplicates the Ferrand theorem; and verified the hypotheses and objects used at each step. All introduced arguments are within the item. The three off-unit statements used as generic tools are declared in split_report.tool_uses; Mathlib leaves need no additional route declaration.

## Unfinished work

None within this one-level split. The cited existing unsplit nodes remain work for their own items. No Lean was written and no compiler, Lake or local DAG preflight was run.

## Validation

The first required server dry run completed with OK and preflight passed. A final source-table check corrected the finite-presentation step’s tag from 01T1 to 01TX; the statement and proof argument did not change. The corrected delivery is submitted to the required dry run again before pushing.
