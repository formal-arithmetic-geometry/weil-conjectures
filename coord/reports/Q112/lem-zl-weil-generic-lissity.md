# Worker report: lem-zl-weil-generic-lissity

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-weil-generic-lissity.json`: statement, now split into six steps; no Mathlib match. The statement and its hypotheses are unchanged.
- `citations.json`: one literal statement quotation for each of the 25 step/node citations.
- `searches.jsonl`: results logged by the required search command, including the second semantic phrasing.

There are **0 new nodes and 0 Mathlib leaves**. All ingredients already have nodes. The geometry below is a short consequence of integral base change, closedness, and incomparability, rather than a new lemma duplicating those ingredients.

## Attachments

None. I read `lean/WeilConjectures/WeilSheaf/LisseLocus.lean`, particularly `AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar` at line 111, and its proof contains no `sorry`. However, `WeilSheaf.Category` defines its carrier as a directly constructed pro-etale Qbar sheaf. Its category docstring asserts a finite-field-of-definition interpretation, but the theorem does not supply a comparison with the exact common-stage constructible heart in this item's definition node. The current `def-weil-weil-sheaf-complex` instead records `Sheaf.Paper.SfWeilSheafComplex`. I therefore did not claim an exact attachment. I also searched the exact item tag and the generic-lissity concept throughout `WeilConjectures/`.

## WANTED

None.

## Problems found and corrected

The imported item had no proof. Its common-stage coefficient convention is essential: the finite-coefficient generic-constancy theorem and `fin2-lem-lisse-dense-open` cannot be applied directly, and the direct pro-etale theorem is not by itself evidence for an attachment. The existing `lem-per-qbar-generic-duality-model` explicitly uses the required adic common-stage category and already supplies the geometric generic-open assertion. I use precisely that assertion, not any material inside its proof or its duality conclusion.

The blueprint paragraph 4 proposes descending strata and intersecting conjugates. Beneath that paragraph's finite-field-model requirement, I use the closed-image construction `U_0 = X_0 \\ p(X \\ W)`. This is a choice of argument below the unit level, not a departure from the unit's affine-line reduction or chapter route. It makes the model open directly and avoids a separate Galois descent theorem. No statement dispute or statement change is needed. Reducedness is retained; the argument actually uses no extra reducedness assertion about the geometric base change.

## Unfinished work

None in this one-level split. The cited existing unsplit nodes remain their own items. No Lean was written, no compiler was run, and the read-only repository and launcher were not edited.

## Blueprint and duplicate searches

I read the current `main-20261015` chapter, unit and the statement/proof of `thm-zl-relative-line-stratification`, as well as the chapter/unit records. I searched the whole DAG for generic lissity, dense lisse opens, finite-stage stratifications, integral closed maps and incomparability, and ran `tools/blueprint_refs.py search` for `lisse`, `dense open`, `integral`, and `generic lissity`. The existing finite-coefficient loci do not express the adic assertion; the existing generic duality model is the appropriate stronger geometric tool. The item's `blueprint.from.place` already identifies paragraphs 1 and 4; `same_as` remains an actual searched empty list. No new nodes were created, so there are no new/existing tag pairs to distinguish.

## Not duplicates

No new nodes. In particular I did not introduce a geometric generic-lissity node, a closed-image dense-open node, or a Frobenius-restriction node: the former already follows from a stronger cited node, and the latter arguments are written in the item's steps.

## Review by Q112

I read the current ancestor proof, paragraphs 1 and 4, and Deligne's Weil II (1.1.1), printed pp.146-147, for the integral, rational and algebraically closed lisse conventions. The references to SGA in Deligne's historical discussion are not dependencies of this split. The split follows the current blueprint using the existing adic category nodes. I read Bhatt-Scholze Definitions 6.8.8 and 6.8.10 and Proposition 6.8.14 in the local PDF to check that finite-stage rationalization and constructible cohomology are the relevant coefficient conventions. There are no new-node sources to review.

For step 1 I checked the inverse-system and fixed-pair definitions: on the empty site the zero system represents the unique heart object; its restricted isomorphism is still invertible. This proves the exact prescribed empty-scheme clause, including the specified choice of open, rather than omitting it as vacuous.

For step 2 I opened `lem-pod-separated-finite-type-base-change` and `lem-weil-pbc-finite-type-over-noetherian`; they give respectively the geometric finite-type/separated hypotheses and Noetherianity. I checked Stacks 01T6 (`morphisms.tex`, `lemma-finite-type-noetherian`). I opened the full statement of `lem-per-qbar-generic-duality-model`: its first assertion allows a singleton family of objects and gives all cohomology sheaves lisse on a finite disjoint decomposition of a dense open containing every generic point. Its base field can be our algebraically closed k, ell is invertible, and the nonempty hypothesis is supplied by step 1. `lem-per-adic-heart-pullback-fibres` uses exactly the same common-stage heart, so H^0(F) is F. The disjoint pieces can use a single finite compositum by `def-weil-algebraically-closed-coefficients`; disjoint union of their normalized systems proves lissity on W. Zero ranks and unequal component ranks are allowed. I have not inferred a global lisse lattice on a general nondisjoint cover.

For step 3 I opened the integral-morphism definition and integral-base-change lemma. The latter is a ring statement, so the step applies it on the explicitly displayed affine charts, not as a black-box statement about morphisms. Algebraicity of k/k_0 supplies integrality. I checked Stacks 01WM (`morphisms.tex`, `lemma-integral-universally-closed`) and 02JK (`algebra.tex`, `lemma-base-change-integral`): `pqf-lem-integral-univclosed` supplies exactly closedness of the image of the bad closed set. The set inclusion p^{-1}(U_0) subset W follows immediately from the definition of the removed image.

For step 4 I checked the statements of `lem-sc-noetherian-closed-subset-finite-components`, `lem-sc-scheme-sober`, the component definition and `pqf-lem-incomparability`. The first, applied to the entire closed space, gives the component covering, not just finiteness of an unspecified list. Sobriety supplies their generic points. I read Stacks 01IS (`schemes.tex`, `lemma-scheme-sober`), 0BA8 (`properties.tex`, `lemma-Noetherian-irreducible-components`), and 00GT (`algebra.tex`, `lemma-integral-no-inclusion`). The proof explicitly shows that points above a base generic point are themselves generic; it does not incorrectly assume this for an arbitrary morphism. Incomparability applies only after we know the two comparable primes have the same contraction for an integral affine map. A generic point cannot have a strict generalization, by maximality of its irreducible component and uniqueness of the generic point. The final closure argument proves density on every component, even if X_0 is reducible or disconnected. This is a short application of the cited assertions and definitions, so it is marked elementary; none of those assertions has been hidden as an uncited theorem.

For step 5 I opened the lisse definition, `lem-weil-pbc-etale-locally-constant-open-pullback`, `lem-per-lisse-completed-system-comparison`, and `lem-per-adic-heart-pullback-fibres`. The locally constant theorem is stated for sets; I use it on the underlying finite-level sheaves only. The already linear transition maps restrict with their module structures and isomorphisms unchanged. The completed-system node explicitly supplies compatibility of the lisse-system realization with pullback, rather than confusing naive discrete non-torsion pullback with adic pullback.

For step 6 I opened the geometric Frobenius definition, the integral completed-pullback composition theorem and the common-stage operation/fixed-pair definitions. `lem-pod-integral-pullback-composition` is for arbitrary scheme morphisms with ell invertible; it does not require a k-morphism, which matters for semilinear Frobenius. I checked its source place, Stacks 099N and the composition formula 0D6D recorded in that node. The affine formula explicitly proves the commuting square. At a common finite coefficient stage the composition comparison rationalizes, and the resulting morphism and inverse define a class in the common-stage category. Pulling back theta and theta^{-1} gives inverse maps. The argument only asks for the existence of this restricted Weil structure and does not claim a separate coherence theorem without citing it.

I checked B--E of `coord/delivery-errors.md` against the actual files: there are no statement-only new nodes with hidden proofs, no new or duplicate definitions, no invented Mathlib queries, no clause merely renamed as a new node, and no coefficient-category identification by fiat. Every step's uses are in proof_deps, and citations.json quotes the corresponding statements verbatim. All six steps are below 2000 characters. I checked that the large generic-model tool does not depend on this item, so this reuse introduces no cycle. Tool uses outside the unit are declared in split_report for the maintainer to judge. The edge cases checked were the empty source/model, a zero sheaf, rank zero or different ranks on different components, a reducible model with intersecting components, and a model whose components split after extension. In particular none requires geometric irreducibility, normality or a Frobenius map linear over k.
