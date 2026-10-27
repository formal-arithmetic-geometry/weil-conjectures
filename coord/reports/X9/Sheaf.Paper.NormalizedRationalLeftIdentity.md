## What changed

Proved `normalized_rational_left_identity` from the existing restricted ring identity,
scalar object normalization, raw-localization action and component normalization.
A private generic lemma translates the construction records into the proved ring
cocycle records before specializing to completed coefficients. This avoids repeatedly
reducing the concrete coefficient construction.

The rational scalar-object transport and the passage from an integral scalar unit
to the prescribed rational unit are proved in separate modules. The latter uses
faithfulness of the intrinsic full-subcategory inclusion and raw localization.
One new obligation identifies the underlying multiplication-normalized integral
unit with the specified integral unit. It concerns one scheme and one integral
object, with no exceptional functor, compactification, rationalization or coefficient
comparison-square conclusion. Existing signatures and public imports are unchanged. The helper statements use
only the normalized construction-data definitions.

Validation: `lcompile.py --all` compiled all four modules together with exit code 0.
There is exactly one `sorry` in the packet, in the named integral normalization step.

## Proved and sorry left

Closed the item hole
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_rational_left_identity`
(node `lem-sf-normalized-rational-left-identity`). The item module has zero holes.

Added one hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_integral_scalar_unit_underlying`
in `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` (node
`lem-sf-normalized-integral-scalar-unit-underlying`). This is a decomposition: one
upper hole closed and one strictly smaller integral normalization hole added.

The separate theorems
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_integral_scalar_unit`
and
`WeilConjectures.ConstructibleExceptionalCoefficients.rational_scalar_object_transport`
are proved, with no holes. No other holes are added.

## No longer needed

No original import was removed. The general theorem/module
`lem-sf-rational-left-coefficient-localization` /
`Sheaf.Paper.RationalLeftCoefficientLocalization` is not needed by this identity proof:
its finite-sum arrow normalization and composition hypotheses are stronger than needed.
The identity uses `F.rationalAction` only on the localized integral unit arrow.

`lem-weil-finite-free-completed-scalar-comparison` is no longer a direct proof dependency
of the item. It is retained as a dependency of the integral normalization step.
The completed-line canonical restriction remains part of that step's stated plan;
its module is not imported by the proved localization glue. No module is withdrawn,
and no claim is made that these dependencies have no other consumers.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted the comparison between the adjunction-normalized
multiplication unit and the chosen intrinsic integral unit. The existing ring
cocycle yields the law for `R.scalarIdentity`, whereas the conclusion uses
`sfRationalScalarUnit`. The new integral normalization step isolates that comparison;
the proof of the rational identity and its localization glue are complete.

The current rework row was checked. The item source is present, and its attachment
and dependencies are preserved. The unit route is unchanged. Identity embeddings
and zero objects are included; the integral normalization statement requires no
geometric characteristic assumption on its scheme.

The normalization step's plan uses
`lem-pur-completed-line-tensor-coherence` as a scalar-normalization tool: its
`canonical_restriction` identity clause identifies the exact chosen integral unit.
The compatibility unit's other declarations do not supply that comparison. This
preserves the compatibility unit's route rather than bypassing it.

A dependency-graph check found a pre-existing cycle outside this packet:
`lem-pc-ring-hom-extension-differential` has the adjacent node as a proof dependency,
while `lem-pc-ring-hom-extension-differential-adjacent` has the former as a statement
dependency. This is reported for the maintainer; neither node is changed.

## New nodes

`lem-sf-normalized-integral-scalar-unit-underlying`: the multiplication-normalized
restricted integral unit agrees with the chosen intrinsic integral unit before
localization. Its source and complete K-flat/adjunction proof are in its docstring.

`lem-sf-normalized-integral-scalar-unit`: faithful lifting of that underlying
comparison and raw localization give the prescribed rational unit component.

`lem-sf-rational-scalar-object-transport`: the object-level rational scalar formula
identifies the unchanged localized integral scalar object. No change records are
needed; no shared interface was changed.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
