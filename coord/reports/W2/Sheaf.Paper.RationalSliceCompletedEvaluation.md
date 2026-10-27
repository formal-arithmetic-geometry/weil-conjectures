## What changed

Proved `WeilConjectures.IntegralOnSlice.restrictionHom_complete` in
`Sheaf.Paper.RationalSliceCompletedEvaluation`. The proof installs the structures supplied by
`ScalarLocalization.exists_triangulated_scalarLocalization`, then projects the internal-Hom
completeness clause of the already stated `rationalThickEvaluation`. The second argument is
complete on the same actual site; no boundedness or constructibility is introduced. All existing
signatures and definitions are unchanged. Updated step 7 of the owning node to record this
application and its scalar-localization dependency.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.IntegralOnSlice.restrictionHom_complete`.
This is a proof from existing stated dependencies, including the still-unproved
`rationalThickEvaluation`, as required by stage 3. It adds no holes and no declarations.

Three existing holes remain, all owned by `lem-sf-rational-slice-completed-evaluation`:

- `WeilConjectures.IntegralOnSlice.restrictionCompletion_bijective`.
- `WeilConjectures.IntegralOnSlice.restrictionComplete`.
- `WeilConjectures.IntegralOnSlice.rationalSliceCompletedEvaluation`.

## No longer needed

No nodes or modules are pruned: the other holes still require their planned dependencies.
The internal-Hom completeness substep needs no new local-completeness or Cech/Koszul bridge;
its exact conclusion is already the fifth conjunct of `rationalThickEvaluation`.
No imports removed. Scalar-localization triangulation is already publicly re-exported by
`RationalThickEvaluation`.

## Where the brief, the DAG or earlier work was wrong

The internal-Hom helper's docstring describes a long local-completeness argument, but the
existing stated rational thick-evaluation theorem already supplies exactly this clause.
Its rational-category structure assumptions can be discharged by the existing scalar-localization
theorem. This preserves the unit route and the original generality, including every slice,
unbounded first arguments and zero objects. No new statement or definition repair is needed.

Validation: the final module compiled on the project server in 33.2 seconds with no
warnings. The import-direction check accepts the existing RationalThickEvaluation import.
Neither rationalThickEvaluation nor scalar-localization triangulation reaches the item
in the stated dependency graph. No new module, definition, theorem, or hole was added.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
