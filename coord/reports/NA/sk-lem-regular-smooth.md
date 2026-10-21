## Worker report

### Files written

- `dag/nodes/sec-smooth-purity/sk-lem-regular-smooth.json`: item, statement unchanged, status split, five proof steps; no complete Mathlib match. Existing Mathlib leaves supply the localization and dimension algebra.
- `dag/units/sk-lem-regular-smooth.json`: only `realized` and `realized_by`, assigning the unit statement and its single proof paragraph to this item. The unit statement and route are untouched.
- `citations.json`: nine entries, one for each step/node citation, with verbatim excerpts from the existing node statements.
- `report.md`: this report and direct worker review.

### Attachments

No exact attachment for the item. The two apparent candidates are `AlgebraicGeometry.IsRegularImmersion.smooth_comp` and `AlgebraicGeometry.IsRegularImmersion.ringKrullDim_stalk_add`, in `lean/WeilConjectures/AlgebraicGeometry/Morphisms/RegularImmersion.lean:145,165`. Their bodies contain no sorry, and their conclusions give the two clauses, but their regular-immersion hypothesis has a genuine codimension-zero mismatch described below. I have not claimed an attachment or edited their Lean.

Existing attachment, unchanged: `AlgebraicGeometry.smooth_of_isRegular` belongs to `lem-trf-regular-perfect-field-smooth`, `lean/WeilConjectures/AlgebraicGeometry/Regular.lean:129`. That existing node already records this theorem; step 2 reuses its statement.

### WANTED

None. All necessary blueprint, Stacks and Mathlib sources are available in the named read clone.

### What was wrong

The imported proof did not cite the regular–smooth criterion or the local dimension calculation. Its componentwise dimension discussion did not itself establish the current statement's equality at every stalk. I expanded the same route into an affine quotient, localization at the two corresponding primes, localization of the regular sequence, and the general regular-sequence dimension theorem. The current item statement agrees verbatim with the main-20261015 source and has not been changed.

The older detailed sibling `lem-pur-regular-immersion-smooth-structure` points to the smooth-regular curve result `lem-sc-smooth-regular`. A curve-only statement is insufficient here. I used the existing unrestricted statements `lem-trf-regular-perfect-field-smooth` and `lem-weil-pbc-smooth-scheme-over-field-regular` instead; I did not edit that sibling. Its current `blueprint_update` states the same smoothness and stalkwise-dimension assertion in the fixed purity setting, so it is recorded in `blueprint.same_as` rather than recreated or used circularly.

### Upstream definition mismatch

The current convention node `sk-def-purity-conv` says that each point of Z has an affine neighbourhood in X with a regular sequence of length c, explicitly allowing c=0. In contrast, `IsRegularImmersion` at lines 90–95 of the upstream file requires a length-c weakly regular generating sequence at every point of X, including outside Z. For c=0 it demands that the ideal sheaf be zero even outside Z.

Explicit counterexample to equivalence of these hypotheses: let k be any perfect field, let X be the disjoint union of two copies of Spec k, and let Z be the first component. The component inclusion is a regular closed immersion of codimension zero in the current convention, and X and Z are smooth and regular. At a point of the second component, the defining ideal is the whole nonzero local ring. The only length-zero list is empty, and its generated ideal is zero, so the upstream class cannot hold. The two theorems therefore do not give the item under all its hypotheses. This is a definition mismatch in the attachment candidate, not a false statement of the item; the split retains the allowed c=0 case. The differing positive-c, separated finite-type definition `def-pur-regular-immersion` is not substituted for the item's current convention.

### What could not be finished

Nothing remains mathematically open in this one-level split. There are no new nodes to queue and no Lean edits or compiler invocations. Dry-run and delivery results are recorded below when completed.

## Not duplicates

No new nodes. Searched the whole DAG by regular-immersion/regular-sequence/perfect-field/localization concepts and Stacks tags, and the whole blueprint with `tools/blueprint_refs.py search` for `regular sequence`, `perfect field` and `regular immersion`. Existing algebraic leaves and the existing general regular–smooth criterion were reused. The item itself is the nearest blueprint ancestor; its detailed sibling is recorded in `same_as`, not recreated. No new/existing same-tag pairs arise.

## Mathlib search review

The sandbox initially contained only `searches.jsonl`, not a split or report. I retained and read all four prior search records from 2026-10-21. Their hits were smoothness definitions/instances, smooth field extensions and an elliptic-curve file, not the complete item. I then ran a second semantic phrasing for the immersion/stalk-dimension assertion, a grep for the regular-sequence localization/dimension declarations, and a Loogle pattern with `ringKrullDim` and `RingTheory.Sequence.IsRegular`. All seven actual records, with their exact query strings and service results, are included in the item's `mathlib_searches`. All services answered; none is recorded as unavailable or invented.

The new grep and Loogle hits give the algebraic dimension theorem, not smoothness of a general regular scheme over a perfect field or the complete scheme assertion. I read `Mathlib/RingTheory/KrullDimension/Regular.lean:210–214` and `Mathlib/RingTheory/Regular/Flat.lean:65–80`; the exact dimension formula and prime-localization statement are already represented by `lem-trf-regular-sequence-dimension-formula` and `lem-weil-pbc-weakly-regular-sequence-localization-prime`. No duplicate leaves were created. The full item is not marked Mathlib.

## Review by NA

I read the main-20261015 item statement and its proof file, the stored unit and chapter, the current `sk-def-purity-conv` regular-immersion paragraph, the detailed sibling's `blueprint_update`, and the two apparent upstream attachment proofs and their defining class. The item has a perfect field, smooth X, regular locally-finite-type Z, and a regular closed immersion of pure codimension c. It does not assume Z nonempty, c positive, or that a chosen z is closed. The five steps respect those hypotheses. The older stored unit has the componentwise formulation; the current source has the stalkwise formulation, which this split proves without altering the unit record's statement or route.

For step 1 I opened `def-weil-scheme-over-base`: its statement expressly identifies an S-morphism by equality of the composite structure morphism. This is the only elementary step. Smoothness of a_X is just a hypothesis. The definition does not assert a new smoothness theorem.

For step 2 I opened `lem-trf-regular-perfect-field-smooth` and its exact project declaration, and read Stacks Tag 0B8X (`varieties.tex`, `lemma-dense-smooth-open-variety-over-perfect-field`, including the equality of loci and its proof). The cited node states the regular–smooth criterion for locally finite type schemes, without requiring finite type, separatedness or nonemptiness. Perfectness, regularity and local finite type are all hypotheses of the item. Thus it applies to a_Z as it stands; no finite-type or curve-only criterion is smuggled in.

For step 3 I opened all four cited statements. The regular-immersion paragraph in `sk-def-purity-conv` supplies the length-c regular generators around the point of Z and explicitly includes the empty sequence. `def-weil-closed-immersion` explicitly gives the affine quotient description. `lem-weil-pbc-affine-open-stalk-localization` explicitly identifies each ring stalk with localization at its corresponding prime, including the germ map. `lem-weil-pbc-localization-at-prime-of-quotient` explicitly identifies the quotient of the localized ambient ring with the localized quotient and specifies the map on fractions. I read the associated Stacks Tag 00CT (`algebra.tex`, `proposition-localize-quotient`) and checked the 01HV/01QO references against the existing nodes. The ambient point is i(z), the quotient prime lies in A/J, and its inverse image p contains J; none is confused with a fibre ring.

For step 4 I opened `lem-weil-pbc-smooth-scheme-over-field-regular` and `lem-weil-pbc-weakly-regular-sequence-localization-prime`. The former states regularity of every local ring and local Noetherianity, not just the curve case. I read Stacks Tag 056S (`varieties.tex`, `lemma-smooth-regular`) and its proof. The latter node accepts weak regularity and membership in p and concludes an actually regular sequence in A_p. Its Mathlib source at `Regular/Flat.lean:75–80` has exactly this conclusion. Membership follows because the f_j generate J contained in p. The local ring at an actual point is nonzero; no assertion is made at a point outside Z. This avoids the upstream c=0 defect.

For step 5 I opened `lem-trf-regular-sequence-dimension-formula`, read its Mathlib theorem at `KrullDimension/Regular.lean:210–214`, and read Stacks Tag 00KW (`algebra.tex`, `lemma-one-equation`) underlying the familiar successive dimension drop. The cited node assumes a Noetherian local ring and a regular sequence, precisely what step 4 supplies, and concludes quotient dimension plus sequence length equals ring dimension. Step 3 supplies the actual quotient isomorphism, not merely an image containment. The equality between the extended ideal and the ideal of the localized generators is written out using fractions. Dimension invariance under the displayed ring isomorphisms is explained by the bijection on prime chains. The step does not replace a non-elementary comparison by the word "transports".

The statement dependencies name the regular-immersion convention, schemes over a base, smoothness, regularity, local finite type and ring Krull dimension. The two off-unit generic geometry results are declared in `split_report.tool_uses`: they are exactly the regular–smooth criterion and the smooth-implies-regular fact that the unit's proof invokes. Neither changes its route. The algebraic and stalk facts are existing Mathlib leaves. No new node restates an item clause or hides its argument. Every cited node's statement was opened, and citations.json quotes the precise content (or whole statement) actually used; a definition node is not cited for an unrecorded theorem.

Small cases checked: c=0 with i the identity gives the same local ring on each side; c=0 with the inclusion of a proper clopen component gives the same stalks on Z and shows why attachment fails; the empty Z gives vacuous dimension equality and smooth empty structure morphism via the general criterion; a line in A^2 at its generic point gives dimensions 1=0+1, while a closed point on the line gives 2=1+1; the origin in A^2 gives 2=0+2. These checks also show why global component dimension cannot be substituted for stalk dimension. The proof uses no rationality of z, no algebraically-closed-field restriction and no characteristic-zero restriction.

I checked delivery-errors B–E against the written steps: no new nodes or duplicate definitions (B, C5), all non-elementary facts have existing-node citations and matching hypotheses (C1/C4, E1), no circular citation to the detailed sibling (C6/D4), and the affine quotient/regular-sequence calculation carries the dimension argument itself (D1–D5). The statement is preserved, so there is no silent weakening or source correction. Every non-elementary step has fewer than 2000 characters, and none hides an additional lemma. The corrections made during this review were to reject the tempting attachment and replace the imported componentwise discussion with the explicit local algebra calculation.
