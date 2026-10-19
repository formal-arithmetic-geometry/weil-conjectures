# N3: lem-coef-simplicial-sm7-generator-extension

## Files written

- dag/nodes/sec-six-functors/lem-coef-simplicial-sm7-generator-extension.json: existing statement, now split into seven steps. Statement and statement dependencies retained.
- dag/nodes/sec-six-functors/lem-coef-parametrized-adjunction-corner-lifting.json: new statement, Mathlib leaf, CategoryTheory.ParametrizedAdjunction.hasLiftingProperty_iff, Mathlib/CategoryTheory/LiftingProperties/ParametrizedAdjunction.lean:164-172 (hypotheses at 30-40).
- citations.json: verbatim statement quotations for every step citation.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the item id, SM7, cotensor, pushoutProduct, pushout-product and hasLiftingProperty_iff found no project declaration with the whole assertion. The parametrized-adjunction project extension concerns conjugate isomorphisms, not this lifting theorem. Upstream master is reference material only and was not treated as finished evidence.

## WANTED

WANTED: Lurie, Higher Topos Theory, Remark A.3.3.4, for lem-coef-simplicial-sm7-generator-extension. The parent item's source names this reference, but no HTT document is archived in literature/. Nothing was downloaded or written to literature/. The proof is explicitly marked agent-written; its non-elementary categorical input is read from the pinned Mathlib source.

## Findings and route

The imported item has no proof or lean_audit entry. It needs neither cellular generation nor cofibrant generator domains: its two right lifting equalities suffice. I retained the statement exactly. There is no STATEMENT-DISPUTED finding.

Read the chapter sec-six-functors and unit sk-prop-sf-biduality-general, and the current main-20261015 prop-coef-integral-exceptional-adjoint.proof.md. This auxiliary foundation is already assigned through the projective-model-calculus ancestry to the derived coefficient adjunction in paragraph 2. The paragraph itself does not prove the generator criterion, so I do not claim it as an external proof of that criterion. The split fills that ordinary prerequisite without changing the chapter, unit, or ancestor route. The item is not the unit's key node; no unit file was changed.

## Not duplicates

No Stacks tag is asserted for the homotopy-theoretic item or the general adjunction theorem, so there are no same-tag pairs. Whole-DAG statement searches for parametrized adjunctions, corner lifting, lifting adjunctions, Leibniz constructions and pushout/pullback lifting did not find the new assertion. Whole-blueprint searches using blueprint_refs.py for cotensor, simplicial model, pushout, lifting, adjunction, parametrized, bifunctor and pullback corner found no duplicate. Matches about ringed-topos adjunctions, Frobenius corners, and specific simplicial local-fibration results do not state the general three-category theorem. Project Lean searches likewise found no generic corner-lifting declaration outside Mathlib.

lem-coef-parametrized-adjunction-corner-lifting vs lem-coef-simplicial-sm7-generator-extension: the new leaf is an arbitrary parametrized-adjunction lifting equivalence, without a model structure, generators, or a simplicial compatibility conclusion. The generator extension is proved in the item's steps 2-4; it has not been moved into the leaf.

## Review by N3

I read delivery-errors.md B-E in full, the item and each cited statement, and the pinned Mathlib source of the new leaf. The imported source is the current blueprint paragraph described above. For the new node I read ParametrizedAdjunction.lean:30-172, including the correspondence of squares and fillers, and checked its theorem at line 164 against the statement. Its H and R are Mathlib's F and G, and its three arrows are f₁, f₂, f₃. Only the indicated pushout and pullback are required; there is no implicit completeness or smallness assumption. The new statement introduces its objects, defines the natural Hom bijections and the lifting property, and states the relevant universal properties inline. It has no proof sketch or proof dependencies and is a Mathlib leaf, not a new unsplit restatement of the item. Source line numbers were checked in the actual pinned checkout. All recorded searches were run through msearch.py and their hits read; the complete generator criterion is absent, while LeanSearch, Loogle and LeanFinder find the generic corner theorem.

Step 1 uses the actual enriched tensor/cotensor representing isomorphisms in def-coef-simplicial-tensor-cotensor and takes their vertices. The natural ordinary Hom bijections give H(K,A)=K tensor A and R(K,X)=X^K, exactly the hypotheses of the new leaf. The complete category in lem-coef-simplicial-boundary-collapse-test supplies the required pullback and pushout. The resulting corner is X^L to X^K fiber-product Y^L, with the common target Y^K; the variance and arrows are checked, not guessed.

Step 2 uses only the weak-factorization-system clause in lem-coef-simplicial-boundary-collapse-test and the assumed generator products. For p a trivial fibration, the cotensor corner lifts against S, is therefore itself a trivial fibration, and hence lifts against every cofibration. This gives the cofibration assertion by the exact left lifting characterization. Step 3 uses the same cited WFS statements with p any fibration and b weak: S still detects a *trivial* fibration corner, so every cofibration works. Step 4 instead tests T, giving a fibration corner; the left class is now the trivial cofibrations. These distinctions ensure that no weak-equivalence closure under arbitrary pushouts or transfinite colimits was smuggled into the argument. Neither generator has to be cofibrant at its source.

Step 5 uses the tensor representing isomorphism from the definition node with the parameter variables interchanged, then applies the same leaf to H(A,K)=K tensor A and R(A,X)=Map(A,X). The apparent opposite ordering of the two pushout summands is harmless for a stated reason: maps out are the same compatible pairs. The target pullback is Map(A,X) fiber-product over Map(A,Y) with Map(B,Y), as required for the SM7 corner. No model compatibility is used in establishing this equivalence, avoiding circularity.

Step 6 cites both the Kan-model statement and the model-category WFS definition: horns are in the left class of Kan fibrations, boundaries detect trivial fibrations including dimension zero, and the preceding product cases give the needed fillers. For the trivial mapping-corner conclusion I checked the separate cases c weak and p weak. Step 7 proves the converse, testing arbitrary trivial fibrations for cofibration membership and arbitrary fibrations for trivial-cofibration membership. A weak monomorphism is a trivial cofibration in the Kan model, so it lifts against every Kan fibration. The cited nodes really state the model structures and lifting characterizations used, rather than just naming those notions; quotations are in citations.json.

For small cases I checked identity c, b or p, the empty simplicial set and the boundary of Delta^0. Identity corners give the expected identities, the empty-boundary test is included, and all pullbacks are finite diagrams in an already complete category. The general leaf also allows identity arrows and needs only the chosen pushout/pullback; it imposes no nonexistent global limit assumptions on its three categories. Empty S or T cause no gap: the corresponding right orthogonality equality is then an assumption on all maps, and the same proof remains valid. There is no domain-cofibrancy or local Kan hypothesis to verify. No new statement depends on the item, so there is no circular dependency through the leaf. The proof uses no off-route statement besides the already stated foundational model and Kan conventions; those nodes are in the same assigned unit, and the generic result is a Mathlib tool. No SGA source is used.

Every proof step is below 2000 characters. The two comparison steps cite the general theorem rather than hiding a new identification lemma in a long step. Every non-elementary ingredient is a cited statement. I checked the elementary, duplicate, item-clause and Mathlib alternatives before creating the single genuine general-purpose Mathlib leaf. The full logical content remains in the item. No live file, launcher, Lean file or compiler was modified or invoked.

## Unfinished

Nothing in the one-level split remains unfinished. The standard downstream nodes retain their own statuses. Required server dry run and delivery follow this report.
