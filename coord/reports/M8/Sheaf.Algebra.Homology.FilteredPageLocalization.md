## What changed

The original theorem `CategoryTheory.filteredPageLocalization` is proved by assembling
`filteredPageDescent` and `filteredPageStationary`, with the original statement and complete
`FilteredPageLocalizationData` contract unchanged.

The public definitions and data move to `FilteredPageLocalizationSetup`, publicly reexported
by the original module. A bundled `FiniteFilteredPageModel` retains the normalized witness
and its laws as structure projections. This replaces expensive repeated nested choices in
three definitions; the change is recorded in
`coord/changes/M8-filtered-page-normalized-model.md`. The witness comes from the proved
normalized construction, with no data hole. The new witness records omit unused generated
constructor injectivity lemmas; the original structures retain their generated API.
All original public signatures are retained.

`FiniteFilteredGradedComparison` proves comparison for every filtration step by finite
induction through short exact sequences. `FilteredPageDescent` proves the homotopy and
localization descent, including ordinary cohomology and first-page normalizations.
`FilteredPageStationary` proves the quotient-image/graded-image comparison, the core and
representative normalizations, chain naturality, successor compatibility, and all localized
naturality clauses. `StationaryLocalizationNaturality` proves the generic extension from
localization generators followed by finite descent through stationary successor pages.

All writes are in this sandbox. No source-library module or quarantine archive is changed.
No other group's module needs adaptation. The blueprint unit's realized statement and
steps are empty, so this internal route change bypasses no required unit realization.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.filteredPageLocalization` (`lem-kun-filtered-page-localization`).

New proved declarations are `CochainComplex.finiteFilteredModule_graded_comparison`,
`CategoryTheory.finiteFilteredPageModel_nonempty`, `CategoryTheory.filteredPageDescent`,
`CategoryTheory.localization_stationary_naturality`, and
`CategoryTheory.filteredPageStationary`. All private helpers are proved.

Original holes closed: 1. Holes added: 0. Split off with `sorry`: 0.
There is no `sorry` left in any delivered Lean module. This is a proof, not a decomposition
into retained holes. Existing imported declarations retain their current project proofs.

Validation: all six delivered modules compiled together through `lcompile.py`. A second
compile checked the final proof cleanup; the only remaining style warning was a long
line, which has been wrapped. No compiler or tactic warnings remain in the proof code.

## No longer needed

The cone/filtered-acyclic route is replaced by finite induction through short exact
filtration-step sequences. The right-fraction route is replaced by the proved generic
localization-generator argument and successor transport. The original proof dependencies
`lem-pur-quasi-iso-cone-acyclic`, `lem-sp-degreewise-filtered-acyclic`,
`lem-kun-filtered-quasi-isomorphism-fractions`, and
`lem-pc-left-localization-fraction-representation` are unnecessary for this proof.

Removed direct proof imports:

- `WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic`;
- `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions`;
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`;
- `Mathlib.CategoryTheory.Localization.CalculusOfFractions`;
- `WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`;
- `Sheaf.CategoryTheory.BoundedFilteredComplexPageCore`;
- `WeilConjectures.CategoryTheory.Abelian.Filtration`.

The last three are redundant direct imports: the normalized construction still supplies
these definitions and uses the core. Mathlib's calculus-of-fractions module also remains
transitively imported by the already-proved two-out-of-three interface. The core node is
not pruned. Its old direct tool approval, along with the unused cone and acyclicity
approvals, is removed from the item's `tool_uses`; no new approval is inserted.

A source-import traversal with the sandbox overrides removes these modules from this
item's import closure:

- `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions`;
- `Sheaf.Algebra.Homology.FilteredQuasiIsoRightCancellation`;
- `Sheaf.Algebra.Homology.FilteredQuasiIsoRightOre`;
- `WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic`;
- `WeilConjectures.CategoryTheory.DegreewiseFilteredStableQuotient`;
- `WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap`;
- `WeilConjectures.CategoryTheory.FilteredCohomologyImageNormalized`;
- `WeilConjectures.CategoryTheory.FilteredCohomologyImagePresentation`;
- `WeilConjectures.CategoryTheory.FilteredComplexGradedHomology`;
- `WeilConjectures.CategoryTheory.FilteredComplexPositivePages`;
- `WeilConjectures.CategoryTheory.FilteredComplexSpectralSequence`;
- `WeilConjectures.CategoryTheory.FilteredStableSubquotient`;
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.

This is pruning from this proof's closure. Other consumers may still require them; no
source declaration, module or DAG node is withdrawn or deleted. All remaining original
statement dependencies are preserved, and the new node dependency records describe the
actual proof route.

## Where the brief, the DAG or earlier work was wrong

The planned cone and fraction arguments are valid but longer than necessary given the
available declarations. Graded comparison follows directly from short exact sequences;
localized naturality needs only the generators and stationary successor equations.

The original nested witness choices were an elaboration bottleneck. Keeping one
irreducible record witness makes its dependent normalization fields practical to use.
The chosen witness is not claimed definitionally equal to the former nested choices;
the change record explicitly reopens the usual definition review for affected targets.
No mathematical statement is disputed and no target statement is changed.

Edge cases use the same categorical proofs: zero complexes and the zero ring, steps past
the upper bound or below the lower bound, and arbitrary unbounded cochain degrees. The
quotient-image/graded-image isomorphism itself does not require a stationary bound.
The final page bound additionally dominates the normalized differential-stabilization
bound, so the source cycle inclusion used for descending naturality is an isomorphism.

## New nodes

`def-kun-filtered-page-localization-data` records the preserved public definitions, the
jointly normalized model, and the full and partitioned data records in
`FilteredPageLocalizationSetup`.

`lem-kun-finite-filtered-graded-comparison` is the finite-filtration quasi-isomorphism
comparison. Its proof uses the already-proved source helper
`HomologicalComplex.HomologySequence.quasiIso_τ₂`, implementing the long-exact-sequence
and five-lemma argument, followed by finite induction.

`lem-kun-filtered-page-descent` records the proved descent prefix and its ordinary and
graded derived normalizations.

`lem-kun-stationary-localization-naturality` is the generic proved generator-extension and
successor-descent lemma; it has no filtered-complex-specific hypothesis.

`lem-kun-filtered-page-stationary` records the proved normalized stationary suffix, relative
to fixed descent data. Its quotient, representative, chain-map and successor calculations
are explicit private proofs, not assumptions.

The existing node is updated only in its proof route, proof dependencies, proof origin,
Lean attachment, and removal of unused direct tool approvals. All new nodes have the
three Mathlib search kinds recorded from this session and inherit the original unit and
chapter. Blueprint searches found no matching imported blueprint statement for these
auxiliary lemmas. Change record: `coord/changes/M8-filtered-page-normalized-model.md`.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
