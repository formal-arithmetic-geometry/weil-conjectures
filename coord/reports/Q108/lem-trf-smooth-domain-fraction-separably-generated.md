# Stage-1 report: lem-trf-smooth-domain-fraction-separably-generated

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-domain-fraction-separably-generated.json`: item, statement unchanged, split in four steps. No Mathlib match for the full assertion; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the six step/node citations.
- `searches.jsonl`: actual Q108 search-command log. The item's inherited search records are retained, and the new logged queries/results are appended to its `mathlib_searches`.

## Attachments

No attachment for the item. Searching `lean/WeilConjectures/` by its exact id and by smoothness, fraction fields and separable generation found no declaration giving the required implication. `Algebra.smoothAtPrime_bot_of_isSeparable_fractionRing` in `RingTheory/SmoothAtGenericPointOverField.lean` proves the converse direction. `FieldTheory.exists_smooth_subalgebra_fraction_field` likewise starts from separability. Neither proves this item. `Algebra.Smooth.isReduced_of_field` in `WeilConjectures/Mathlib/RingTheory/Smooth/StandardSmoothOfFree.lean` supplies only an existing ingredient, already represented by `lem-sc-smooth-algebra-reduced-field`; it is not an attachment of the item.

## WANTED

None. All sources used are present locally.

## Findings and corrections

The statement is correct, including over imperfect fields. Its conclusion is separability of a possibly transcendental extension (every finitely generated intermediate extension is separably generated), not algebraic separability. No statement dispute is needed. The existing 07ND DAG node states only the reverse implication, so citing it for this item would be C4. Similarly, the existing 037X node states only separability implies the existence of a smooth fraction-field model. I use neither as a black box.

The proof follows the forward argument in `literature/stacks-project/algebra.tex`, Tag 07ND (`lemma-smooth-at-generic-point`), which Tag 037X (`lemma-localization-smooth-separable`) invokes. I made the characteristic-zero case explicit because the existing geometric-reducedness criterion 030W requires prime characteristic. I wrote out the two localization hints of 04KN rather than treating its omitted proof as an available theorem. In particular, the existing node `lem-weil-pbc-localization-preserves-reduced` only treats localization at a prime, so I did not cite it for an arbitrary multiplicative subset of a tensor ring.

The nearest current blueprint ancestor is `lem-trf-local-term-locality`, as confirmed by `tools/blueprint_refs.py ancestor`. I read its statement and proof in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`, and the chapter/unit records. The item retains its existing detailed ancestry through the Temkin separating-parameter input. Blueprint searches for `separable` and `smooth field`, together with DAG searches for 037X, 07ND and the algebraic ingredients, revealed no imported blueprint node stating this implication. Existing generic algebra nodes suffice; none was duplicated. The split does not change the chapter or unit route.

The logged LeanFinder searches used two phrasings; Loogle, LeanSearch and Mathlib grep were also run and their hits read. `Mathlib/RingTheory/Smooth/Field.lean` proves separably generated implies formally smooth, not its converse. `FractionRing.isSeparable_of_isLocalization` in `DedekindDomain/Instances.lean` already assumes the needed fraction-field separability. `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` assumes perfectness absent here. These do not make this item a Mathlib leaf. No Lean was written or compiled.

## Unfinished work

None at this split level. Existing dependency nodes retain their own stage states. No new unsplit statement is needed.

## Not duplicates

No new nodes were created. In particular, I reuse the existing smooth base-change, smooth-algebra reducedness, tensor-localization, characteristic-zero separability and positive-characteristic separability-criterion nodes.

## Review by Q108

I read Stacks 037X and both directions of 07ND in `algebra.tex`, then checked the forward proof's actual inputs against the statements of the DAG nodes. I also read 00T4 (`lemma-base-change-smooth`), 00TT (`lemma-characterize-smooth-over-field`), 04KN (`lemma-geometrically-reduced-permanence`), 00DK (`lemma-tensor-localization`), 00D2 (`lemma-tensor-with-bimodule`), 030W (`lemma-characterize-separable-field-extensions`), and the characteristic-zero sentence in 00TX. For the affine reducedness ingredient I read `varieties.tex`, 056T (`lemma-smooth-geometrically-normal`), and the project declaration `Algebra.Smooth.isReduced_of_field`. There are no new nodes whose sources need separate review.

Step 1 uses `lem-weil-pbc-char-zero-field-extension-separable`, whose statement explicitly covers every field extension of a characteristic-zero base. The given F is a field with the induced k-structure, so it satisfies these hypotheses. For positive characteristic the characteristic of a field is prime, which is the only remaining case.

Step 2 uses clause (1) of `lem-weil-pbc-smooth-ring-map-base-change-composition`, which says exactly that R' tensor_R S is smooth over R' for ANY base map R to R'. Setting R=k, S=A and R'=L gives L to L tensor_k A. `lem-sc-smooth-algebra-reduced-field` then gives reducedness of this commutative smooth L-algebra. Its statement requires a field L and smoothness, both now in hand; it adds neither a perfectness hypothesis nor a domain hypothesis on the tensor product. I read both statements, and copied them verbatim into citations.json. The smooth-reduced node is a generic off-unit tool, declared in split_report.tool_uses.

Step 3 uses `lem-weil-pbc-localization-tensor-over-base` only for the module localization it actually states: R=k, its algebra=A, T=A minus zero, M=A and N=L. The fraction-field hypothesis identifies T-inverse A with the specified F, not an unrelated field. Swapping the two tensor factors and using the explicit formula identifies the resulting module isomorphism with the ring localization: products of fractions of pure tensors map to products because (a/s)(b/t)=ab/(st). The proof then supplies the reducedness calculation itself. If (b/s)^n=0, some t in T kills b^n; hence (tb)^n=0 in the reduced source, so tb=0, which is exactly the zero test for b/s. Thus no theorem about arbitrary localization of reduced rings is silently imported. This is a few-line elementary calculation from the cited module localization and fraction definitions, not a new node. It does not assume B is a domain or that every denominator image was already a unit in B.

Step 4 uses `lem-weil-pbc-geometrically-reduced-extension-separable` for precisely its full statement: k has characteristic the prime p, F is a field extension, and F tensor_k L is reduced for EVERY field extension L/k by steps 2--3. Its conclusion is the nonalgebraic separability needed here. Clause (2) of `def-weil-pbc-separable-field-extension` translates that conclusion to the exact intermediate-field assertion in the item. Both quoted node statements say this explicitly. The criterion is a generic off-unit field-theory tool, declared in split_report.tool_uses.

I checked edge cases A=k, a polynomial algebra k[t], and a finite separable field A over k; the same argument works with an empty transcendence basis in the algebraic cases. In imperfect characteristic p, a nontrivial purely inseparable finite field A/k fails smoothness and acquires nilpotents after adjoining the requisite p-th roots; this explains why dropping smoothness or using algebraic separability for k(t)/k would be wrong. The localization calculation also works for n=1 and for tensor rings with zero divisors. The zero ring A is excluded in the statement. Every step is shorter than 2000 characters, and no non-elementary lemma is hidden in a long step.

Against B--E: the statement is self-contained using the same three existing notion nodes; no statement-only new node carries a hidden proof; TeX uses ordinary single escapes when decoded; sources name tags and labels. Every non-elementary ingredient is cited, citations use statements rather than proofs, and the elementary fraction calculation is written out. There is no clause moved to a new node, no new duplicate, and no strengthened hypothesis. `proof_deps` is exactly the union of the step citations; citations.json has an unaltered verbatim statement for each citation. The server dry run passed the preflight, including the DAG and split checks; the final report correction is revalidated before pushing.
