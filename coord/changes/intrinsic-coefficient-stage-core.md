# Finite coefficient stage module split

## Reason

The item compiled logically but repeatedly exceeded the 60-second per-file bound.
After extracting the already-proved scalar normalization and improving local
interfaces, split its finite-stage part into `Sheaf.Paper.SfCoefficientStageCore`.

## Old

The finite-stage definitions, scalar comparisons, exactness and tensor coherence
were all in `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`.

## New

Their fully qualified names, signatures, attributes and data bodies are unchanged.
The original module retains every original public import and publicly imports the
core, so existing importers continue to see the same API. The core's one new public
theorem, `SfAlgebraicallyClosedCoefficients.associator_commShift`, is the previously
proved private helper; it adds no hole. The core uses the separate named rational
associator intermediate. The pair construction stays in the original module, with
its natural-transformation pentagon reconstructed from the exported component
cocycle. DAG attachments of the moved definitions and normalization/exactness
statements now name the core.

## Users

All existing importers of `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` use its
public re-export. No existing importer source is changed. The item is held by D2;
no module held by another group is edited.

## Status

Open: delivery checks and independent review verify the split and public re-export.
