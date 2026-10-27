## Reason

Prove the assigned quotient-section comparison, including compatibility with the
fixed successor balancing. The static interface checker requests a change record
for new file-local commands and the new tensor helper module.

## Old

`AlgebraicGeometry.Scheme.adicPerfectQuotientSectionComparison` had one `sorry`.
The tensor helper module and its public naturality theorem did not exist.

## New

The original theorem has the identical signature and a complete proof. A new
helper module supplies a proved public tensor-quotient naturality theorem; its
other helpers are private and proved or explicitly constructed. The new theorem publicly imports its Mathlib tensor-quotient API. Other proof
imports are private. The added universe, open, and local reducibility commands support
private calculations inside these files and do not change existing public
declaration signatures, attributes, instances, definitions, or public imports.
No source-library module or target is modified. No extra hypothesis is imposed.

## Users

`Sheaf.Paper.AdicPerfectQuotientSectionAdjunction` is the sole direct importer
of the item. Its use of the comparison keeps exactly the same type and needs
no adaptation. It compiled unchanged against the delivered proof and helper
module; the temporary copy used for this check was removed. `Sheaf.Paper.AdicPerfectQuotientSectionComparison` privately
imports the new tensor helper module and uses its naturality calculation.
There are no other direct importers and no forced adaptations.

## Status

landed 20261026T222648-L-679743 2026-10-26 (merge of deliver/G1/Sheaf.Paper.AdicPerfectQuotientSectionComparison)
