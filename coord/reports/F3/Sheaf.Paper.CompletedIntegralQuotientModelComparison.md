## What changed

Filled `WeilConjectures.completedIntegralQuotientModelComparison` in
`Sheaf.Paper.CompletedIntegralQuotientModelComparison`, retaining its exact signature and
all four original public imports. Added only private, proved helpers and private proof
imports. No existing definition, instance, public attribute or declaration signature changed.

The proof constructs the independent-universe sheaf tensor comparison and the normalized
successive-extension isomorphism. The actual completed quotient presentation then gives
isomorphisms at every degree and finite level. Cokernel-tensor augmentations are epimorphic;
cancellation assembles the level isomorphisms into a natural strict tower isomorphism.
Both signed Roos coordinates identify its augmentation with the specified beta. Private
equations for completed coefficient projections, the Roos isomorphism, quotient product
projections and the unit diagram keep
these constructions abstract during elaboration. All these helpers are proved here. The K-flat
change-of-rings theorem and the existing integral scalar extension uniqueness clause descend
the comparison and prove the required unit equation.

The proof imports are `ChangeOfRingsTensorCancellationIndependentCoefficients` (tensor API),
`ChangeOfRingsKFlatAllIndependentCoefficients` (the extended representative is K-flat),
`CochainCoefficientArrows` (normalized ordinary extension adjunction),
`SystemScalarCoherence` (restriction composition), `IntegralScalarExtensionWellDefined`
(actual scalar sections, transitions and uniqueness), `IntegralOperationsWellDefined`
(the existing cone-map comparison), `PrincipalQuotientCompletionExists`
(quotient transition and naturality), and the source-library `BifunctorSingle`
(the degreewise single-complex tensor comparison). All are proof-only imports.
The node's proof and proof dependencies record this route. The proof-scope command
changes are documented in `coord/changes/F3-completed-integral-quotient-comparison.md`;
no consumer adaptation or definition repair is involved.

Validation: `lcompile.py` compiled the complete file in 49.8 seconds with zero local
holes. The original theorem signature and all four public imports were checked verbatim;
the node JSON parses and every Lean line is at most 100 characters. No new axioms or
public declarations were added. The delivery compiler also completed its module axiom
probe (`SHEAF-PROBED 2`) in a 47.6-second check. An ordered sandbox check compiled the
item in 51.0 seconds and its unchanged direct consumer,
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`, in 34.0 seconds. The temporary consumer
copy was removed; no consumer changes are delivered.

## Proved and sorry left

Closed: `WeilConjectures.completedIntegralQuotientModelComparison`
(`lem-weil-completed-integral-quotient-model-comparison`), one original hole.
Added: zero holes. Remaining in the item: zero holes. Split off: zero statements.
Every private helper is proved in this module; no new module or axiom is introduced.
This is a proof from existing library declarations, not a decomposition into new obligations.

## No longer needed

No original public import is removed. The following original direct proof dependencies are
unnecessary for this argument:

- `lem-pur-quotient-scalar-comparison-descent`, module
  `Sheaf.Paper.QuotientScalarComparisonDescent`: the actual scalar extension's
  existing uniqueness clause descends the constructed strict comparison directly.
- `lem-weil-pbc-localization-universal-property`: the required localization uniqueness is
  already packaged in `integralScalarExtensionWellDefined`.

These two direct edges are removed from this node's proof dependencies. Neither dependency is
claimed globally unreachable or withdrawn; no Lean file or adopted source declaration is deleted.
All statement dependencies and the blueprint unit's realized statements and steps are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or required statement repair was found. The standard same-universe
sheaf tensor helpers do not instantiate directly at the independent site and coefficient
universes of this theorem. The private proof supplies the needed comparison in those universes
and checks its actual sheafification generators. The DAG's general tensor/descent plan is
made concrete by epimorphic tower assembly and the already normalized scalar extension
uniqueness clause; no target hypothesis or conclusion changes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
