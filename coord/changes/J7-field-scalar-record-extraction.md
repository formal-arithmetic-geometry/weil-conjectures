# Field scalar record extraction for proof decomposition

## Reason

The identity and composition lemmas need ScalarData, Identity and Successive in their
statements, while the main theorem must import those lemmas. Keeping all definitions
in the theorem module would create an import cycle. Move the seven existing records
and abbreviations to FieldScalarNormalizedData and publicly re-export that module.
This extraction precedes any compile failure and serves the mathematical decomposition;
it is not a workaround for the compiler time limit.

## Old

Sheaf.Paper.FieldScalarNormalizedSystems declared Compositor, ScalarData,
IntegralCompositor, SystemCompositor, Successive, Identity and Family, followed by
field_scalar_normalized_systems with one sorry.

## New

The seven declarations have identical names, universes, binders, fields, bodies and
visibility in Sheaf.Paper.FieldScalarNormalizedData. The original module publicly
imports it and keeps the original theorem signature and docstring. The theorem is
proved from three strict subresults, with an explicit proof of the ramification clause.
There is no target-statement change, weakened field, or new choice definition.
The three existence results are consumed only inside the main existence proof.
Family explicitly permits independently chosen bases, and its functors and comparisons
are fixed up to the normalized tensor isomorphisms already specified in the records.

## Users

python3 tools/downstream.py Sheaf.Paper.FieldScalarNormalizedSystems reported zero
current Lean importers. A whole-library textual search found no external use of the
theorem or Family. This does not authorize withdrawal: the DAG parents still need it,
and the original theorem and attachment are preserved. All previous public imports
are re-exported through FieldScalarNormalizedData, so even a future or quarantined
consumer keeps the same public vocabulary. No consumer adaptation is needed.

The new SingleInclusion, IdentityComparison and SuccessiveComparison modules import
only the data module for their statements. The original module imports these three
privately, giving an acyclic dependency order.

## Status

landed 20261025T163741-L-815329 2026-10-25 (merge of deliver/J7/Sheaf.Paper.FieldScalarNormalizedSystems)
