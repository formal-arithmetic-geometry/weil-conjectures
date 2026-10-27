# Stage-1 report: lem-trf-polynomial-localization-order-reflection

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-polynomial-localization-order-reflection.json`: statement, split into six proof steps; not a Mathlib leaf. Original statement, provenance, prior searches and source retained. Appended searches actually run with the required command.
- `citations.json`: eighteen verbatim statement quotations, one for each node citation in each numbered step.
- `report.md`: this report. Sandbox-only search log and working script are ancillary files, not node deliveries.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves and existing split algebraic tool nodes cover every non-elementary input.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag and by polynomial/localization/order and maximal-ideal-power terminology. The nearby polynomial-localization declarations do not state every clause of this item. No project declaration was identified as an exact attachment. Mathlib regularity alone is not the order-reflection assertion.

## WANTED

WANTED: Hironaka, *Certain numerical characters of singularities* (1970), Lemma 14, printed p.169, archival PDF for this node's historical source. Its path in the inherited source is absent locally. The present proof is explicitly agent-written from the available Stacks inputs; it does not claim to have read the missing Hironaka PDF. No missing source is needed to check this proof.

## Findings and corrections

The statement is correct as imported; no STATEMENT-DISPUTED correction is required. Its old source already describes a synthesis, not a verbatim assertion of 031E or 00NO. I supplied the contraction argument, rather than citing either tag for a conclusion it does not state. The claim includes arbitrary primes over the maximal ideal, not only closed points, so the fibre is a prime localization of the polynomial ring over the residue field, rather than necessarily a maximal localization. The residue extension need not be separable. No coefficient field, completeness, excellence, characteristic-zero or algebraic-closedness assumption is introduced.

I read the current chapter/unit records and the latest blueprint ancestor statement and proof in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`. This latest ancestor now follows contracting correspondences; the item's recorded long historical alteration branch remains provenance. I have not changed the chapter, unit, or ancestor theorem. This item only supplies the inherited auxiliary local-algebra input. Its `blueprint.from.place` was already specified; `same_as` remains empty. Searches of the full imported blueprint for `regular graded`, `polynomial.*regular`, `dimension-base-fibre`, `maximal-ideal order`, `00NO` and `00ON` gave no equivalent blueprint node. Searches across the full DAG did find all the existing algebraic inputs now cited. In particular I reused the general canonical graded criterion instead of creating a new associated-graded injection lemma or repeating the item's contraction clause in a new node.

The full DAG was searched by 031E, 00NO, parameter/basis terminology, polynomial regularity, flatness, Noetherianity, quotient localization and dimension-base-fibre. I read every cited node's statement. The tempting `lem-trf-smooth-local-tangent-cone-extension` cannot be used here because it assumes Q-algebras essentially of finite type. `lem-trf-local-polynomial-tangent-extension` only covers the origin prime for one variable. `lem-trf-mvpolynomial-noetherian` only asserts the Z-coefficient case; the proof instead cites the existing arbitrary finite-type Noetherian permanence node. These distinctions avoid a hidden hypothesis or an overbroad citation.

## Mathlib searches

All new search invocations are in `searches.jsonl` and were read. LeanFinder searches for polynomial local order preservation and for regular parameters under a flat local extension returned localization maximal-ideal identities, weak-regular-sequence flat ascent and related smoothness results. LeanSearch for the graded injection returned flat tensor injectivity and faithfully flat maps, neither of which compares the two maximal-ideal filtrations. Loogle `"IsRegularLocalRing", "Polynomial"` returned `Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal`. I read `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean:35` onward: it proves regularity, not contraction of powers. The two grep queries in RegularLocalRing and Loogle `"maximalIdeal", "pow", "comap"` found no contraction theorem. These are genuine nonmatching results, not unavailable services. The previous item's detailed searches are retained and agree with this conclusion.

## Generic tool uses

`lem-weil-pbc-flat-over-regular-with-regular-fibre` is generic commutative algebra used to prove regularity of S after explicitly identifying its closed fibre. `lem-sfb-regular-local-graded-cotangent-criterion` is the generic canonical Sym-to-graded criterion, used for both regular local rings. They belong to other units but replace no step of this item's unit: the unit has no competing local-algebra assertion. They are declared in `split_report.tool_uses` for maintainer review. All other off-unit statement citations are existing Mathlib leaves. No top-level `tool_uses` maintainer field was written.

## Not duplicates

No new nodes were created, so there are no new/existing tag pairs to distinguish.

## Review by Q118

I checked the statement against the actual Stacks statements and proofs in `literature/stacks-project/algebra.tex`: 031E (lemma-flat-over-regular-with-regular-fibre), 00ON (lemma-dimension-base-fibre-equals-total), and 00NO (lemma-regular-graded). The parameter-generating argument of 031E supplies the intended route, and the canonical generator map in the proof of 00NO supplies the required identification of the graded map. I also read 00FN (lemma-Noetherian-permanence), 00CT (proposition-localize-quotient), 00OQ (proposition-finite-gl-dim-polynomial-ring), and section 00DM (section-tensor-algebra); morphisms.tex 01U5 (lemma-flat-characterize) checks the polynomial projection's affine/local interpretation. There are no new nodes whose sources need a separate check.

Step 1 takes finite-type Noetherian permanence from `lem-weil-pbc-finite-type-algebra-noetherian`, and localization permanence from `lem-weil-pbc-localization-noetherian`. The specified finite polynomial algebra meets the first hypothesis with zero quotient ideal. `def-weil-pbc-localization-at-prime` gives the actual local ring and maximal ideal. `lem-nagata-polynomial-projection-flat` asserts flatness of the scheme projection, not directly module flatness; I therefore use `def-weil-flat-morphism` for flatness on local rings and explicitly cite `lem-weil-pbc-spec-map-stalk-localization` for the identification of those ring maps. This last citation was added during self-review to remove an implicit affine-stalk theorem. The inverse map R_m -> R is written down, and contraction of the maximal ideal and injection of residue fields are verified explicitly.

Step 2 uses the coefficientwise polynomial definition to identify the quotient; a polynomial is in mP precisely when each coefficient is in m, by expanding its finitely many coefficients. It applies `lem-weil-pbc-localization-at-prime-of-quotient` with I=mP and the prime q/I, whose inverse image is q. The statement of `lem-weil-pbc-polynomial-ring-field-regular-ring` covers ALL prime localizations, so the fibre is regular without a maximality assumption on the image prime. Both R and S are Noetherian local, flatness was proved in Step 1, and the fibre is regular, exactly the hypotheses of `lem-weil-pbc-flat-over-regular-with-regular-fibre`.

Step 3 takes the local dimension equality from the equivalent local formula in `lem-weil-pbc-flat-height-formula`. The base and target are Noetherian and the map is flat; localization at their maximal ideals changes neither ring. By the regular-ring definition we may choose d base generators and e fibre generators. The displayed subtraction argument proves that their images/lifts generate n; no freeness or splitting theorem is assumed. `lem-weil-pbc-regular-local-cotangent-dimension` states precisely that the cotangent dimensions equal the Krull dimensions for these regular local rings. A spanning list with that many members is therefore a basis, over k and L respectively.

Step 4 uses the STATEMENT of `lem-sfb-regular-local-graded-cotangent-criterion`, which names the canonical multiplication map and its isomorphism, not merely an abstract polynomial-ring isomorphism. Both applications meet the nonzero Noetherian local hypotheses: S is nonzero because q is a proper prime. `lem-weil-pbc-symmetric-algebra-free-module-polynomial` identifies the symmetric algebra of a standard finite free module with its polynomial algebra, and `lem-weil-pbc-symmetric-algebra-universal-property` transports this along the basis isomorphisms, with inverse composites checked on generators. Finally, from the polynomial definition and k -> L injective, a surviving monomial coefficient proves injectivity. Thus there is no appeal to an unproved flat-map cotangent injection, no characteristic/separability condition, and no abstract-isomorphism-to-canonical-map inference.

Step 5 uses only the associated graded definition to turn the injectivity already proved in Step 4 into an induction on the exponent. The inductive assertion, base a=0, downward inclusion of powers, zero class, and reverse inclusion by products are all explicit. Step 6 equates the sets defining the suprema and covers the zero element. These two steps are elementary consequences of preceding steps and definitions, not new lemmas. Every non-elementary step is below 2000 characters; none hides a source's omitted sublemma.

I tested s=0 (q=m and S=R), R a field with a nonmaximal fibre prime (all positive base powers are zero), a DVR base with q=mP (e=0), and a prime obtained by adding an irreducible polynomial to mP (possibly inseparable residue extension). The basis argument still works in all these cases. The exponent zero and zero-element order are explicitly covered. As a guard against accidental overgeneralization, a flat local map alone would not suffice: k[[t]] -> k[[u]], t -> u^2, has a nonregular closed fibre and fails order reflection. Our Step 2 establishes the missing regularity hypothesis before it is used.

All eighteen entries of `citations.json` are entire statements copied verbatim from the cited files; they support the specific uses discussed above. I checked B1--B10, C1--C8, D1--D5 and E1--E7 of delivery-errors against the final split: no new-node duplication, clause relocation, circular dependency, hidden hypothesis, degreewise weakening or unsupported source attribution remains. The report makes no Lean proof claim. No repository or launcher file was changed; no compiler, Lake or local preflight was run.

## Unfinished work

None in the stage-1 split. Its dependencies retain their own statuses. Independent maintainer review and subsequent Lean work are outside this delivery.

## Validation

The server `review_split` check passed on the initial six-step draft. Full delivery dry run and direct push are performed after this report is written; their exact outputs are authoritative.
