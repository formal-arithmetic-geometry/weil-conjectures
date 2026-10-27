## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-pur-common-stage-finite-object-lifting.json`, the item, statement, split; no Mathlib match. Also `citations.json` and the command-generated `searches.jsonl`.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. The essential-surjectivity witness is an assumption of the item. Taking a finite compositum, conjugating maps by the specified comparisons, and composing inverse arrows are steps, not separate lemmas.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and common-stage, finite-object and finite-tuple terminology. `FilteredTwoColimitCharacterization.comparison_characterization` concerns a general coherent cocone comparison and does not state this item's specified coefficient functor and compositum control. The field-stage pointers concern a different realization of coefficients. Neither is an attachment.

## WANTED

None. This is explicitly an agent subargument; no external theorem or unavailable literature is claimed.

## Findings and changes

The item was statement-only and has no released repair note. Its statement and all statement dependencies are retained. I filled the proof, proof dependencies, agent origin, status and split report, kept the ancestor reference, and appended the new searches. The earlier seven Mathlib search records were read and retained, including the corrected Loogle query after its identifier error. The new logged searches used LeanSearch, Loogle, LeanFinder in two phrasings, and grep. Hits give essential-surjectivity definitions, filtered set colimits, finite (co)product constructions and special profinite diagrams; none is a one-line specialization proving this whole item. Mathlib `Functor.EssSurj` and `objObjPreimageIso` in `Mathlib/CategoryTheory/EssentialImage.lean`, lines 106 and 130, explain precisely the assumed witness; they do not supply the common-stage construction or its coefficient data.

No statement dispute, source error, unfinished branch, or route departure was found. The old blueprint assertion of invertibility alone is not treated as a proof of this item.

## Blueprint and duplicate search

Read the chapter `sec-smooth-purity` and unit `sk-def-purity-conv`, the current main-20261015 `def-pur-section-invariant.md`, and the current `sec-proetale-coefficients/sk-def-sf-operations/def-weil-algebraically-closed-coefficients.md` and `def-weil-derived-pullback-tensor-hom.md`. Also read the corresponding current DAG statements, which make the representative comparisons explicit. The ancestor command gives `def-pur-section-invariant`; this split realizes its finite-clopen coefficient transport as specified by the item's inherited source place. Searched the whole imported blueprint using `blueprint_refs.py search` for common-stage, finite tuples and essentially surjective, and searched the DAG for common-stage and representative-functor/compositum terminology. The general filtered-two-colimit characterization does not give this coefficient formula or exact field control; existing definitions already provide the category and operation formulas. The adjacent finite-Hom-lifting and field-coefficient-descent items are not used, avoiding circularity.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to justify.

## Review by Q48

I read delivery-errors B through E whole and checked the written node against them. There are no new statement-only nodes needing independent hypotheses, notion dependencies, tags or leaf lines. The item already states every scheme, field, index set, comparison and stagewise essential-surjectivity assumption. I did not change its coefficient category or insert a Karoubi completion. The proof is an agent argument following the current blueprint's raw common-stage definition, rather than an attribution of the calculation to an unverified Stacks tag or to SGA.

Step 1 uses the actual natural pullback/scalar isomorphisms in `lem-pur-integral-operations-scalar-extension` and the natural identity-compatible tower comparison in `lem-weil-scalar-extension-composition`; I read both statements, not their proofs. The integral comparisons are used rationalized exactly as stipulated in the item's hypothesis. The type of the conjugated arrow is checked at both endpoints. All schemes have ell invertible because they are over k with ell different from its characteristic; every tower field is finite inside the fixed closure. This step is marked non-elementary because it invokes those comparison theorems.

Step 2 cites the same two comparison statements and `def-weil-algebraically-closed-coefficients`, whose statement explicitly says representatives are equal when they agree after further extension. I checked the tower identity with a source of type T(N/L)T(L/E)r(E)K and target r(N)T(N/E)K, then checked each inverse in the formula for the transported arrow. Naturality supplies the middle equality and cancellation gives exactly the target category's transition formula. Thus no unstated comparison or equality test is imported. This step is non-elementary for the same reason as step 1.

Step 3 uses the identity compatibility already stated by the integral comparison node and the common-stage definition's composition rule. With all arrows over N the middle b and its inverse cancel; that is an elementary calculation with the supplied functors and isomorphisms. The finite product takes this componentwise, and the empty product has its unique arrow. Step 4 uses the actual algebraically closed pullback clause of `def-weil-derived-pullback-tensor-hom`, including its displayed conjugation formula, rather than treating a definition as a theorem about an unspecified functor. The formulas coincide because the item explicitly fixes those same comparisons.

Step 5 uses the binary compositum finiteness and smallest-subfield assertions explicitly written in `def-weil-finite-subextension-directed-set`. The finite induction starts at Q_ell, so repeated fields, an empty tuple with a nonempty additional list, and an entirely empty list are covered without choosing a nonexisting member. `def-weil-rationalization-karoubi` explicitly supplies a scalar-extension functor into the rational constructible category, so every H_i is an object in the codomain of the hypothesized R_L. Essential surjectivity of R_L is then applied directly as an assumption, not inferred from a missing theorem. For I empty it is applied to the unique empty tuple and still yields K at this very L.

Step 6 uses the pair-category definition's representative identity and composition/equality rules and the scalar-extension identity compatibility. Both representatives really have the same object H_i at L after the identity-extension identification; their products are identities at L. For the E_i endpoint this identity is the extension of its identity at E_i, which verifies the inverse equation instead of merely asserting stage-change transport. The alpha_i from step 5 and their inverses then give an isomorphism to the desired tuple, with the orientation explicitly specified. This remains an empty tuple of inverse arrows when I is empty. No nonempty-index assumption, full faithfulness, field enlargement beyond the compositum, or idempotent splitting was used.

Each step citation has a verbatim supporting quotation in `citations.json`; comparison theorems are quoted in full so naturality and tower compatibility are included. Every proof dependency is used. Each step is below 2000 characters, and no step hides a separate lemma with additional hypotheses. The principal correction made while writing was to spell out the scalar-transition equation and both inverse equations for stage change; a bare claim that the formulas transport would not have met C4/E5.
