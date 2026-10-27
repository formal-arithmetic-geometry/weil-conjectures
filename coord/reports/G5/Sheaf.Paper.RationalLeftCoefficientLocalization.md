## What changed

Filled `WeilConjectures.rational_left_coefficient_localization` in
`Sheaf.Paper.RationalLeftCoefficientLocalization`, without changing its signature.
The proof specializes the given finite-sum arrow normalization to one integral arrow
with coefficient one, and uses the existing rational scalar comparison component
specifications. Applying the localization functor to the integral composition and
unit equations proves the rational equations after explicit heterogeneous transport.
The unchanged integral object represents every rational input; the existing
`integral_residue_tor` theorem supplies its uniform finite-Tor property. Invertibility
of the coefficient prime in residue fields is proved from the finite-field cardinality
and the structure map. Added the private proof import
`Mathlib.Algebra.CharP.CharAndCard` for that calculation, and proved private helpers
for component formulas and transport. Local irreducibility keeps the chosen scalar
comparisons from unfolding while checking the proof.

Removed the unused universe-wrapper public import (with a change record).

Updated the item's DAG proof metadata to record its actual use of the already
existing `lem-weil-scalar-extension-composition` component specifications.

Validation: the final module compiled remotely through `lcompile.py` in 9.6 seconds,
with exit code 0 and no errors or warnings. The theorem signature is byte-identical
to the original; all Lean lines are at most 100 characters.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.rational_left_coefficient_localization`
(node `lem-sf-rational-left-coefficient-localization`).
All five conclusions are proved. Zero holes remain in the item; zero holes were added
and zero statements were split off. This is a proof from existing declarations,
not a decomposition.

## No longer needed

The proof uses all three original declared proof dependencies:
`def-weil-rationalization-karoubi`, `lem-coef-integral-residue-tor`, and
`def-weil-linear-scalar-localization`.

Removed the unused public import `Sheaf.Paper.IntegralScalarExtensionUniverses`:
none of its wrapper declarations occurs in the statement or proof. There are no
current direct or transitive Lean importers of the item, as checked by
`tools/downstream.py`; no consumer requires adaptation. This removes an import,
not the wrapper module or its defining node, which remain available elsewhere.
No DAG dependency is pruned and the unit route is preserved.

Change record: `coord/changes/G5-rational-left-unused-universe-import.md`.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was sufficient. Its proof dependency list omitted the
existing scalar-comparison node whose canonical component specifications implement
the normalization of the associator and unit; the delivery records that dependency.
No statement or definition repair was needed. The construction also handles identity
embeddings, repeated fields, zero objects and empty schemes, since it uses only
functor laws, the component specifications and the unchanged integral representative.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
