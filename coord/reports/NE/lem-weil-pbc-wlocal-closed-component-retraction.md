# Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-wlocal-closed-component-retraction.json` (item, split)
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-wlocal-isClosed-bijOn-retraction.json` (statement, closed Lean declaration)
- `citations.json`

## Attachments

`exists_retraction_of_isClosed_of_bijOn` belongs to the new supporting node; it is closed in `WeilConjectures/RingTheory/ProEtale/WContractible.lean:505-628` and contains no `sorry`.

## WANTED

None.

## Not duplicates

`lem-weil-pbc-wlocal-isClosed-bijOn-retraction` vs `lem-weil-pbc-wlocal-stalk-isomorphism-retraction`: the existing node assumes faithful flatness, extremal disconnectedness, and a closed-point ideal and proves a broader preliminary splitting result; the new node is the closed-component restriction theorem with an explicit closed subset T and component surjectivity/injectivity.

## Review by NE

I read the imported item, the unit and chapter records, the Tag 09AZ proof in `literature/stacks-project/proetale.tex`, and the complete source declaration `exists_retraction_of_isClosed_of_bijOn`. The declaration has the same closed-component restriction conclusion, with the Lean algebra/typeclass packaging; I therefore recorded it as a closed supporting node rather than claiming the natural-language item is an exact attachment. The item’s only step checks each translation: the given ring map induces the R-algebra structure, the prime-localization isomorphisms are precisely stalk bijectivity, the closed-point condition is unchanged, and bijectivity of h restricted to T gives the theorem’s surjectivity and injectivity hypotheses. The final ring map is then the declaration’s retraction and its composition identity is exactly the requested one. I searched the DAG and blueprint for duplicate statements and ran LeanFinder, Loogle, Mathlib grep, and LeanSearch for the supporting node; the first three found no matching Mathlib theorem and LeanSearch was unavailable. I checked the citation quotes against the cited node statements and tested the empty-spectrum and singleton-component edge cases conceptually; the argument reduces to the auxiliary theorem in both cases.

`lem-weil-pbc-wlocal-isClosed-bijOn-retraction` vs `lem-weil-pbc-wlocal-closed-component-retraction`: the supporting node fixes an explicit R-algebra structure and states surjectivity plus injectivity on T, while the item starts with an arbitrary ring map and a single bijectivity hypothesis; the item proves the translation.

`lem-weil-pbc-wlocal-isClosed-bijOn-retraction` vs `lem-weil-pbc-extremally-disconnected-component-section`: the component-section node constructs a section under compactness and extremal disconnectedness, whereas the supporting node assumes a closed component subset already given and proves the ring retraction.

## Second reading by NE

- Item statement: checked against the blueprint ancestor `thm-weil-pbc-qbar` and Stacks Tag 09AZ (`lemma-w-local-extremally-disconnected`), implication (3) to (1); the arbitrary ring map, w-local hypotheses, stalk bijectivity, closed-point contraction, closed component subset, component bijection, and retraction identity agree hypothesis by hypothesis. The zero ring/empty spectrum and one-point field cases satisfy the statement vacuously or by the identity map.
- Step 1: checked against the definitions of w-local spectra and ring-map contraction in Tag 09AZ; the induced algebra structure and component map are the stated map `h`. Verdict: correct.
- Step 2: checked against the localization-at-a-prime definition and the canonical localization map in Tag 09AZ; the assumed stalk bijections are exactly the auxiliary theorem's `BijectiveOnStalks` condition. Verdict: correct and now cites `def-weil-pbc-localization-at-prime`.
- Step 3: checked against the w-local closed-point definition and the component-map hypotheses of the supporting theorem; restriction bijectivity gives both existential surjectivity and injectivity on `T`. Verdict: correct and now cites `def-weil-pbc-w-local`.
- Step 4: checked against the complete closed declaration `exists_retraction_of_isClosed_of_bijOn` in `WeilConjectures/RingTheory/ProEtale/WContractible.lean:505-629`; its conclusion is exactly a ring map `s : S →+* R` with `s.comp (algebraMap R S) = RingHom.id R`. Verdict: correct.
- Supporting node `lem-weil-pbc-wlocal-isClosed-bijOn-retraction`: checked clause-by-clause against the same closed Lean declaration and Tag 09AZ; w-local assumptions, stalk bijectivity, closed-point condition, closed `T`, component surjectivity/injectivity, and retraction conclusion are all present. It is a closed Lean attachment, not a duplicate of the item because it fixes the algebra structure and separates the component hypotheses. Verdict: correct.

Changes made: corrected the item's `created.item` metadata to its own id (the worker had left the predecessor item id); added the localization and w-local definition citations required by steps 2 and 3; added verbatim citation quotes for those dependencies. No mathematical statement was changed.
