## What changed

Filled `WeilConjectures.pbc_integral_completion_matching_on_good` in
`Sheaf.Paper.IntegralCompletionMatchingOnGood` without changing its statement.
The proof chooses an entire-tower K-injective resolution with injective terms,
identifies the normalized inclusion with the standard Roos inclusion, proves it
is a quasi-isomorphism, and cancels the invertible resolution postcomposition.
It constructs the transported ordinary chain augmentation, proves both of its
coordinates from the model-matching hypotheses, and combines the ordinary
comparison normalization, coefficient-factor naturality, the derived-counit
normalization, and the actual-unit normalization.

Added `Sheaf.Paper.IntegralActualUnitRoosNormalization` for the remaining
actual-unit computation. This statement has no integral pullback identification,
no model comparison b, and no model-matching hypothesis. It assumes only an actual
chain augmentation with quotient first coordinates and zero shifted coordinate,
and computes the actual completed pullback unit after a strict resolution.
The inclusion need not be a quasi-isomorphism for this computation. Its source,
complete proof in words, edge cases, and DAG node are included.

Private helpers in the item provide product/cocone extensionality, the canonical
termwise-limit comparison, exact products, and the normalized inclusion's
quasi-isomorphism. The public generic tool `strictRoosDerivation` replaces the
larger existential `strictRoosComparison` interface. It and the functorial
injective-term resolution are generic tools, not changes to the unit's route.
No other existing module or node was changed. A private categorical diagram
lemma keeps the final composition calculation abstract, avoiding repeated kernel
conversion of the large concrete coefficient constructions.

The first delivery attempt did not push because a fresh main-file compile
exceeded 60 s, despite an earlier 53.7 s compile. To reduce concrete conversions,
the already proved coordinate calculation was moved into its own module,
`Sheaf.Paper.IntegralCompletionTransportCoordinates`, and the chosen injective
resolution was packaged in a private structure with its proved properties.
These changes add no holes or changes to any shared interface.

The assigned theorem's signature was compared verbatim with the repository version;
only proof/proof_deps/proof_origin changed in its existing node. All Lean lines
are at most 100 characters. Final profiling verified the extracted module and the packaged main proof; the
main theorem kernel check decreased from about 29 s to 18.5 s. Temporary profiling
options are absent. The delivery
tool checks the final files against the 60 s per-file limit.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.pbc_integral_completion_matching_on_good`
(node `lem-weil-pbc-integral-completion-matching-on-good`).

Added one hole:
`WeilConjectures.pbc_integral_actual_unit_roos_normalization`
(node `lem-weil-pbc-integral-actual-unit-roos-normalization`).

This is a decomposition, not a net hole closure: one upper hole closed and one
strictly narrower actual-unit normalization left. There are no sorries in the
item module, its private helpers, or the proved coordinate module. The new module has exactly one named public
theorem with proof `:= by sorry`; there are no holed definitions.

## No longer needed

No original import was removed. The proof no longer needs
`lem-weil-strict-roos-comparison` / `Sheaf.CategoryTheory.StrictRoosComparison`:
its full normalized derived-functor isomorphism, evaluations, and comparison-map
transport are unnecessary when model matching already supplies b, z and iota.
It uses the smaller proved `lem-weil-strict-roos-derivation` /
`Sheaf.CategoryTheory.StrictRoosDerivation` only for the inclusion's
quasi-isomorphism.

The separate dependency `lem-tw-integral-quotient-augmentation` is not used as a
theorem: the actual chain lift and quotient augmentation are already constructed
in `def-sf-ordinary-integral-pullback-construction`. The proof reads their
mapping-cocone coordinate formulas directly. The declaration and module remain
available; nothing is withdrawn.

The original direct dependencies `prop-weil-pbc-rlim-functoriality` and
`def-weil-pbc-completed-pullback` are retained through the new actual-unit
normalization node. No whole module is withdrawn or claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The original proof plan separates into a substantial
integral-model coordinate argument and an actual-coefficient unit computation.
The latter was not already exposed by the listed theorem signatures; its exact
raw-counit formula is the one new statement. The original unit route is retained.

## New nodes

`lem-weil-pbc-integral-actual-unit-roos-normalization` records precisely the actual
completion unit's representative formula, leaving out all model comparisons.
The source is Stacks Tag 0941, proof of `lemma-derived-limit-is-ok`, and Tag 099N(5),
proof of `lemma-pushforward-Noetherian-case`, with the supplied coordinate and
counit bookkeeping expanded. The proof works for zero complexes, zero coefficient
rings and empty schemes; no geometric nonemptiness or boundedness is required.
There are no change records because no existing signature or definition changes.

`lem-weil-pbc-integral-completion-transport-coordinates` is a proved coordinate
step, extracted to keep each file within the compile limit. It constructs the
transported chain explicitly and proves its chain identity and both coordinates;
it has no K-flatness, resolution or derived-unit assumptions. Its source is
Stacks Tags 08TC and 0941 and Bhatt--Scholze Lemma 6.5.9(4). This module adds zero
holes. No change record is needed: only the item and new modules/nodes change.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
