## What changed

Proved `AlgebraicGeometry.exists_field_curve_completion_insep` with its existing signature.
The only Lean file changed is `Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep`.
The proof uses the stated dense projective completion and geometric normalization results,
then constructs the restricted reduced integral components as pullbacks. Proved private
helpers identify normalization on an open via Mathlib smooth normalization base change,
handle component enumeration, and refine a smooth projective integral component to its
finite separable constant field. No definition, public import, or consumer changes.

The DAG proof and dependency list now follow this argument. The proof handles nonreduced,
empty, zero-dimensional, and reducible schemes uniformly. It retains the unit route.

## Proved and sorry left

Closed 1 existing hole: `AlgebraicGeometry.exists_field_curve_completion_insep`
(node `lem-weil-pbc-field-curve-completion-insep`). Added 0 holes. There are no `sorry`
expressions in the delivered Lean file and no split-off declarations.

Validation: the launcher single-file compiler is used throughout; final validation and
axiom inspection are also performed by `deliver3.py` before pushing.

## No longer needed

Removed these private imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`.
- `Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety` (a re-export of the explicitly
  imported upstream global-sections results).
- `WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`.
- `Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`.

The proof no longer needs the following original proof dependencies:

- `def-weil-pbc-scheme-reduction`: the completion and geometric normalization theorems
  already allow nonreduced input. Its statement-dependency entry is retained.
- `lem-weil-pbc-normalization-projective-components`: finiteness, projectivity and the
  dimension bound are obtained directly from `lem-sc-normalization-exists` and
  `lem-fin-finite-over-projective`.
- `lem-weil-pbc-etale-section-clopen-immersion`, `lem-exc-etale-coproduct-etale`, and
  `lem-weil-pbc-etale-scheme-base-change`: smooth geometric connectedness implies
  geometric irreducibility by the existing regular-scheme API.
- `lem-weil-pbc-reduced-algebraic-normalization-field-change`: open restriction is proved
  directly using Mathlib normalization under smooth base change. Arbitrary or separable
  field-change compatibility of reduced normalization is not needed.
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the Y_i are finite normalizations
  of closed finite-type subschemes of X_K, so their quasi-compactness follows by composition.

These are dependency removals for this proof, not withdrawals of their library declarations.
The existing `tool_uses` list is filtered to remove only the corresponding obsolete entries.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically sound but included unnecessary reduction and separate
etale-section work. The general projective-component theorem fixes its index type in the
scheme universe; our components are indexed by `Fin n`. Rather than change that interface,
the proof invokes its elementary finite-over-projective and normalization ingredients
directly. No target statement or existing definition is changed. No new nodes.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
