# Stage-1 worker report: lem-coef-cartesian-cone-fiber-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cartesian-cone-fiber-comparison.json`: item split into five proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None. No sorry-free declaration in the slopmaster2 source states this item.

## WANTED

- `https://www.math.ias.edu/~lurie/papers/HTT.pdf`, Theorem 3.2.0.1, Proposition 3.2.1.4, and Lemma 3.2.3.3, for the explicit Cartesian fiber-to-cone mapping-simplex comparison.

## What was checked and corrected

The imported statement was compared with the existing cone-generator and arbitrary-base Cartesian-marking nodes. Its hypotheses are retained exactly: S is only a small simplicial set, q is a Cartesian fibration with natural marking, and the conclusion is a weak equivalence in the absolute marked model category, natural for Cartesian-edge-preserving maps. The item has no Lean declaration with the blueprint tag or matching statement.

The existing DAG was searched for the item, its HTT places, and the phrases “fiber-to-cone”, “mapping-simplex”, and “Cartesian cone”. No duplicate node states the comparison, so no child node was created. The four required Mathlib searches were run for this item; they returned only ordinary-category cone/fiber or Grothendieck constructions and no marked simplicial comparison.

Step 1 uses the absolute marked-model criterion and the existing relative sharp mapping complexes and terminal cone construction. Step 2 reads the cone-generator statement literally: terminal cones on standard simplices are the Q^n pieces, and coherent-nerve mapping equivalences identify the enriched calculation. Step 3 checks the hypotheses of the arbitrary-base Cartesian calculus: prescribed-target Cartesian lifts, final-horn marking, restriction fibrations, and pullback natural markings. The simplexwise factorization is the HTT calculation cited in the item source; its choices form the Kan fibers supplied by the relative mapping theorem. Step 4 assembles the simplicial inverse and applies the absolute weak-equivalence criterion, explicitly preserving the “no quasicategory/local Kan hypothesis” clause. Step 5 checks naturality from pullback of Cartesian fibrations and the natural cone formulas.

No new node was needed: adding a node for the fiber comparison itself would merely restate the item. All `uses` are existing statements, `proof_deps` is their union, and every citation quote is copied verbatim from the cited statement.

## Review by Q14

I read the item source and all four cited DAG statements in full. The cone-generator statement supplies the actual Q^n model and the marked natural map; the relative Cartesian statement supplies arbitrary-base prescribed-target lifts, Kan sharp mapping complexes, restriction fibrations, and pullback of natural markings; the absolute marked-model statement supplies the exact test for weak equivalence; and coherent-nerve comparison supplies the mapping-space identification used in the simplex calculation. I checked that the proof never assumes S or its coherent realization is quasicategorical or locally Kan, never changes the coefficient or marking category, and uses the strict fiber X_s with its pulled-back natural marking. I also checked the empty and degenerate simplex cases through the Q^n construction and the terminal-cone clause. The only correction was to replace the imported empty proof by the explicit five-step HTT mapping-simplex argument and to fill the blueprint provenance and citation records.

The mapping-fiber formula node was added to Steps 2–3 after rechecking the simplexwise Cartesian factorization: over each standard simplex, it gives the precise homotopy-fiber comparison and its naturality for Cartesian-edge-preserving maps.

## Second reading by Q14

The statement is unchanged. I downloaded and read `HTT-second-reading.pdf` (HTT, 2017 printing), including the definitions and proof on printed pp. 169–195. This resolves the earlier WANTED entry locally; the shared literature directory remains read-only. No Stacks tag is named by this item: its actual source is HTT, not a Stacks scheme-theoretic result. I compared every hypothesis and the canonical cone map with HTT Definition 3.2.1.2, Proposition 3.2.1.4, the displayed psi preceding Lemma 3.2.3.3, and the derived-unit argument of Theorem 3.2.0.1. The general assertion is true; no STATEMENT-DISPUTED correction or extra hypotheses are needed.

Original-step audit:

- Original Step 1: the absolute marked weak-equivalence test is correct, but it alone supplies no inverse; retained its criterion through the point-model and derived-unit argument.
- Original Step 2: FAIL C3/C4/E1. The coherent-nerve mapping equivalence requires a locally Kan simplicial category, and the quoted ordinary-nerve sentence is not that assertion. The mapping-fiber node requires quasicategory total and base spaces. Replaced by the actual mapping-simplex and rigidification calculations.
- Original Step 3: FAIL C2/C4. Kan does not imply contractible (a two-point discrete Kan complex is a counterexample to that inference); no marked-anodyne inclusion or trivial restriction fibration was identified. Replaced by the explicit cone-cylinder pushout and derived-unit proof.
- Original Step 4: FAIL E5. Restricting independently chosen lifts does not make those choices a simplicial inverse; the omitted arbitrary-base descent is the substance of HTT Section 3.2.4. Replaced by its mapping-space pushout and tower arguments.
- Original Step 5: the canonical map is natural, but naturality does not follow from a functorial choice of Cartesian lifts. Replaced by equality on the cone generators, requiring no choices.

Repaired-step audit (each cited input was opened and its full statement read; `citations.json` contains one verbatim statement quote for every use):

- Step 1: HTT Proposition 3.1.3.7 and boundary-cell node; marked limits/colimits, finite presentation and generating cofibrations checked; PASS.
- Step 2: HTT Remark 3.1.1.10 and relative lifting/small-object nodes; countable domains and input-universe replacement checked; PASS.
- Step 3: relative sharp Kan mapping-complex statement; inverse maps extracted using the two test targets, not contractibility; PASS.
- Step 4: exact simplex inverse-extension statement; prescribed boundary inverse and homotopy match, including zero cells and unions; PASS.
- Step 5: conditional finite relative saturation statement; its fiber-criterion hypothesis is established in Steps 3–4, and Kan right properness proves pushout stability; PASS.
- Step 6: perfect-class recognition statement; all its hypotheses checked before application, including marking reflection for generator-injectives; PASS.
- Step 7: relative lifting criterion and model retract axioms; fibrant objects identified in both directions; PASS.
- Step 8: absolute marked internal-Hom definition; relative tensor, cotensor and enrichment adjunctions checked degreewise; PASS.
- Step 9: marked-anodyne pushout-product statement and Step 3; external products retain inverse homotopies and replacement squares; PASS.
- Step 10: point-model simplicial axiom and Step 9; external pushout product and sharp tensor satisfy the required weak-equivalence assertions; PASS.
- Step 11: relative pullback/natural-marking statement; exact sharp mapping identity makes base composition left Quillen; PASS.
- Step 12: HTT Definition 3.2.1.2 and Proposition 3.2.1.4; cone colimits, actual right adjoint, vertex adjunction and old-face enriched coend verified; PASS.
- Step 13: cone-generator statement and boundary-cell construction; index extension preserves (trivial) cofibrations and handles all four marked-anodyne types; PASS.
- Step 14: HTT Corollary 3.2.1.16 and external-product statement; interval contraction, inverses and two replacement arrows explicitly prove left Quillen; PASS.
- Step 15: HTT Proposition 3.2.1.14 and spine lemma; inner-horn retract argument proves the marked augmentation on every simplex; PASS.
- Step 16: cofibrant-colimit comparison (a)–(c); boundary, skeletal and marking attachments prove the augmentation on every marked object, hence the point adjunction equivalence; PASS.
- Step 17: HTT Section 3.2.2 and Notation 3.2.2.3; mapping-simplex operators, degenerate-edge marking, strict fibers and attaching pushout checked; PASS.
- Step 18: endpoint-prism generation and marked-anodyne pushout product; the explicit retract and product lift include n = 0; PASS.
- Step 19: HTT Proposition 3.2.2.11; stronger relative inductive assertion, Kan factorization and final-fiber lift checked; PASS.
- Step 20: same proposition; restriction to the old face and the relative factorization glue exactly, including empty parameter and empty fibers; PASS.
- Step 21: HTT Proposition 3.2.2.10 and rigidification equivalence detection; ordered vertices make the two blocks full, with the only remaining maps running from old to final vertices; PASS.
- Step 22: all-vertex cocartesian mapping criterion, pinch comparison and composition statements; explicit reversal proves the Cartesian criterion without restricting the test vertex to the source fiber; PASS.
- Step 23: coherent-nerve comparison and pinched-rigidification-resolution statements; mapping composition is compared only after object-preserving locally Kan replacement; PASS.
- Step 24: HTT Lemma 3.2.2.9, existing final-edge node, and Step 22; Cartesian postcomposition over the two point mapping spaces in Delta^n gives the missing square; PASS.
- Step 25: actual Cartesian mapping-fiber node, now applied only over Delta^n with the test vertex in the prescribed source fiber; fiber equivalences and marking reflection written explicitly; PASS.
- Step 26: HTT Proposition 3.2.2.14 and functor-equivalence test; selected full subcategories, base-map reflection and core inverse homotopies prove the relative mapping-test equivalence; PASS.
- Step 27: absolute marked model, functor-equivalence test and inverse triangles; both directions of the fiberwise categorical/absolute-marked equivalence and the induced natural marking checked; PASS.
- Step 28: HTT Lemma 3.2.3.3; final vertex is the literal terminal cone, including n = 0 and empty final fiber; PASS.
- Step 29: the easy computation at the end of that lemma expanded using subset-poset mapping cubes; H, K and the marked mapping-cylinder pushout computed; PASS.
- Step 30: endpoint weak equivalences and final-vertex marked-anodyne statements; the old-face comparison follows by an explicit square after applying L, not by two-out-of-three for the anodyne class; PASS.
- Step 31: HTT Proposition 3.2.1.13 and existing external-product node; product with T(B) gives the marked product-face trivial cofibration; PASS.
- Step 32: HTT Lemma 3.2.3.3; mapping-simplex pushout, old-face coend identity and canonical fiber inclusion complete the induction; PASS.
- Step 33: HTT Lemma 3.2.3.2 and model-nerve localization; conservative right derived functor checked on actual fibrant-diagram representatives; PASS.
- Step 34: HTT Proposition 3.2.3.4; constructed presentation, canonical simplex fiber comparison and the actual point adjunction prove the simplex unit and counit; PASS.
- Step 35: HTT Section 3.2.4 and enriched-diagram homotopy descent; compatible right-derived unstraightening and restrictions retain all mapping spaces; PASS.
- Step 36: HTT Theorem 3.2.0.1 proof on printed pp. 194–195; strict sharp mapping pullback, Kan restriction fibration and the factored-equivalence criterion prove pushout descent; PASS.
- Step 37: same source plus the explicit tower and coproduct clauses of the descent node; products, empty base, inverse Kan towers and skeletal attachments cover every small simplicial base; PASS.
- Step 38: Theorem 3.2.0.1 and the vertex adjunction formula immediately before Lemma 3.2.3.3; the actual derived unit has the displayed composite as its fiber adjoint, so two-out-of-three proves exactly psi; PASS.
- Step 39: cone generators and relative pullback marking; the naturality square agrees strictly on all cone generators and relations, with no choice of compatible lifts; empty total space, point, and n = 0,1 checked; PASS.

New nodes: none. Mathlib leaves: none. The independent LeanFinder query used the vocabulary “homotopy coherent Grothendieck construction”; it returned ordinary-category CoGrothendieck fiber declarations, whose displayed types do not assert the marked simplicial comparison. The separate source grep returned ordinary FiberedCategory declarations only. Both actual outputs are recorded in `searches.jsonl` and the item. The slopmaster2/master source grep found only unrelated GaloisCategory fiber cocones; no attachment was found.

Changes and reasons:

- Replaced the unsupported five-step proof with the 39 checked steps above, without changing the statement or creating duplicate nodes.
- Reconstructed the needed part of the relative-model argument inline, using only its independent inputs. The existing `lem-coef-marked-relative-cartesian-model` includes the arbitrary-base homotopy-pullback theorem and depends on `lem-coef-cartesian-base-equivalence-invariance`, which depends on this item. Citing that full model node, `lem-coef-cartesian-mapping-simplex-presentation`, `lem-coef-mapping-simplex-cone-fibers`, or `lem-coef-marked-cone-straightening-quillen` here would therefore create a cycle. Their needed proofs are explicitly written here from lower statements; those circular nodes are not dependencies, and none was edited.
- Confined the Cartesian mapping-space criterion to simplex bases and compared enriched composition through locally Kan replacement. Thus no quasicategory or local Kan hypothesis is silently added to S.
- Replaced the supposed contractible lifting fibers by the actual mapping-cylinder and gluing calculation, then used the general Quillen unit to identify the specified canonical comparison.
- Rebuilt citations and proof_deps, corrected the source place to distinguish the mapping-simplex lemma from the general derived-unit consequence, and checked the independent 413-node dependency closure contains no path back to this item. The nearest blueprint ancestor and its proof place are unchanged; all inputs remain in the same unit.
- Small cases: S empty (no vertex assertion), X empty (empty cone mapping objects), S a point (defining identity for T), n = 0 and n = 1 with either marking, and empty vertex fibers. No ring or scheme parameter occurs, so field/empty-scheme tests are inapplicable.

Only the sandbox was changed. No Lean code, compiler, Lake, live-project write or agent delegation was used. The first worker's `## Review by Q14` section remains above.
