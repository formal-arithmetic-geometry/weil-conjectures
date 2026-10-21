# lem-sfb-coefficient-projection-square — Q29

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-coefficient-projection-square.json`: statement, now split in five steps; not a Mathlib leaf. No statement or statement-dependency changes.
- No new DAG nodes; no Mathlib leaves created.
- `citations.json`: verbatim statements for every node citation in every step.
- `searches.jsonl`: the search command's actual log, retained. The five fresh searches are appended to the item's inherited search records without deleting the earlier research.

## Attachments

None. The project source has the generic `CategoryTheory.Adjunction.rightAdjointProjectionMap_mate` in `WeilConjectures/CategoryTheory/Adjunction/ProjectionMapCompat.lean:117`, but its tensor-square and mate hypotheses still require verification for these specified coefficient maps. It therefore does not attach to this entire item. The item tag has no declaration in `lean/WeilConjectures`. The pro-etale module-object `derivedPullIso` and `derivedPushHom` definitions were read in `SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:236,247`; their explicit constructions agree with the DAG definitions, and neither asserts the requested tensor/projection square.

## WANTED

None. The proof is marked agent-written: the blueprint paragraph explains the intended coefficient passage but does not supply this calculation. All needed literature and all reused DAG statements are present locally.

## Corrections and scope

The imported statement is well-typed and retained verbatim. Its proof was empty. The repair supplies the missing equality before any invertibility argument. In particular it does not infer equality merely because source and target are canonically isomorphic, and does not assume the push comparison is invertible. The route remains paragraph (3) of the rational proper-base-change detail in the current main-20261015 blueprint.

The existing `def-sfb-module-object-projection-map` source metadata places Tag 0943, `section-projection-formula`, under `sites-modules.tex`; the section and its adjoint-of-counit formula actually occur in `sites-cohomology.tex:13658–13680`. I read that formula in its correct file, together with `sites-modules.tex`, `lemma-tensor-product-pullback` (03EL), and `sites-cohomology.tex`, `lemma-pullback-tensor-product` (07A4), `lemma-derived-pullback-composition` (0D6D), and `lemma-adjoints-push-pull-compatibility` (0FPI). This is a citation-location issue in an existing node, not a statement dispute; that node was not edited.

## Not duplicates

No new nodes. Searches of the whole DAG and blueprint for coefficient/projection, monoidal comparisons, mates and conjugates identified existing reusable statements. In particular `lem-sfb-ringed-comparison-tensor-adjunction` gives exactly the tensor and composite-adjunction normalization needed, while `lem-pd-module-ringed-topos-derived-comparison` transports the actual module-object maps. The existing `lem-sfb-coefficient-pushforward-square` is an underived abelian-sheaf coefficient-unit square, and the etale/pro-etale scalar-mate node concerns a different site comparison and discrete coefficients, so neither was substituted for this assertion.

## Review by Q29

I read the unit and chapter records, the current blueprint `sk-thm-sfb-proper-base-change-rational.proof.md` paragraph (3), the Pull and Push definition files under the current coefficient-comparisons unit, and the Stacks constructions named above. I also read the actual project definitions of the two comparisons and the generic projection/mate compatibility proof. The argument uses ordinary, uncompleted, unbounded derived categories throughout; no SGA source or completion argument enters.

Step 1 uses the complete statement of `lem-pd-module-ringed-topos-derived-comparison`, including the exact symmetric monoidal section-ring equivalence, its preservation of the specified derived adjunctions, and its final assertion identifying the actual pullback tensor map. This is stronger than an abstract equivalence of endpoint categories and prevents changing the projection morphism during transport. Applied to both coefficient sheaves it also identifies scalar extension with the identity-topos ring-change inverse image. The displayed coefficient square in `sk-def-sfb-coefficient-change` supplies compatibility of the structural ring maps. The theorem `lem-sfb-ringed-comparison-tensor-adjunction` explicitly handles two composites related by a ring-compatible 2-isomorphism; here that is the identity square. Its right comparison is the same normalized restriction/pushforward composite as `def-sfb-derived-comap-lower-star-iso`, whose conjugate is exactly `def-sfb-derived-pull-iso`. I checked the standing field and scheme assumptions against the section-ring theorem and selected small site presentations relative to its module-sheaf universe. Flatness is available from the item's exactness assumption, and no extra geometric flatness is used.

Step 2 takes the tensor equation from the *statement*, not the proof, of `lem-sfb-ringed-comparison-tensor-adjunction`. Its comparisons are those transported by the preceding section-ring theorem. Substituting the two composites gives equation (1) with sigma equal to the inverse of the item's c. I checked its source is P_S T_Y(A tensor B) and its target is T_X P_R A tensor T_X P_R B; the order of the maps agrees on both sides. The definition of the module projection map supplies the named d maps.

Step 3 uses the literal conjugate and mate definitions of `def-sfb-conjugate-pull-iso` and `def-sfb-mate-push-hom`, as invoked by the two derived comparison definitions. The composite counit is given in `def-weil-pbc-composite-adjunction`. The step writes the scalar-mate formula and composite-conjugacy counit equation, then explicitly substitutes B=T_X K, moves the scalar unit by naturality, and cancels only the scalar adjunction triangle. Thus the counit identity for gamma is proved in the step; no unstated theorem that a coefficient comparison is monoidal or that two different mates agree is invoked. This is a routine expansion of definitions and naturality, marked elementary.

Steps 4 and 5 use exactly the adjunction in `sk-def-sfb-module-derived-pushpull` and the defining transpose in `def-sfb-module-object-projection-map`. I checked every domain in the two calculations: both original maps start at T_Y(G_R K tensor M), both transposes start at P_S T_Y of that object, and both end at T_X K tensor P_S T_Y M. The left calculation uses (1), (2), c_M sigma_M=1 and tensor naturality; the right uses counit naturality, (2), sigma naturality and the defining transpose of pi^R. Their common final expression is displayed. There is no appeal to the truth of a projection formula to prove this compatibility of its canonical map.

For B–E: no new statements or proof sketches posing as nodes were created; the cited statements were opened and read, and complete verbatim statements are retained in citations.json. No clause was moved to a new node, no descendant of this item was cited deliberately, and the server preflight passed its DAG and split checks. The non-elementary facts are precisely the two cited comparison theorems, declared as generic off-unit tools in split_report. No non-elementary step exceeds 2000 characters. The other steps are explicitly written counit/naturality calculations. I checked identity coefficient change, identity f, either zero input, and scalar extension to the zero ring: the formulas reduce to identity or zero equalities. These checks also show the calculation does not require faithfulness of scalar extension or invertibility of gamma. No empty-scheme, boundedness, properness, constructibility or nonzero-ring hypothesis has entered.

The fresh Mathlib searches were read as returned: the first LeanFinder query gave cartesian Frobenius morphisms and underived presheaf pullback composition; the second gave general mate/counit formulas. Loogle gave general monoidal-adjunction structures, LeanSearch gave unrelated sheafification and resolution equations, and the projection/mate grep in CategoryTheory returned no hits. None states this entire normalized coefficient square. Those generic ingredients do not justify marking the item itself as a Mathlib leaf.

## Unfinished work

None in this one-level split. No new unsplit nodes were needed. Mechanical dry-run and delivery results are reported by the delivery tool.

## Validation

The server review_split check passed with zero new nodes and the two declared tool uses. The required delivery dry run exited successfully with `OK (not pushed)` at d5caaef2560. No Lean compiler or Lake command was run.
