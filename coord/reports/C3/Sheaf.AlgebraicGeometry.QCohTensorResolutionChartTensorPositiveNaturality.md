## What changed

Repair Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality's
incompatible compatibility import. Restore tensorResolutionChartTensorIso_naturality_positive_core
with the adopted signature over the Sheaf chart implementation. Compose the proved
chart summand square, factor transport square and semilinear tensor square with
WeilConjectures' tensorResolution_three_squares. Select the existing chart
instances directly; local reducibility annotations prevent expensive unfolding of the monoidal
structure. The monoidal structure stays locally irreducible during elaboration. Preserve the
statement's local let bindings while introducing its hypotheses, then compose three
independently inferred equations. Only ChartModel and TotalCoherence are public
imports; the four modules supplying proof lemmas are private imports.

Change record: coord/changes/C3-chart-tensor-positive-naturality-import-coherence.md.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero holes left, zero split off.
The restored theorem tensorResolutionChartTensorIso_naturality_positive_core is fully proved.
This is an import-coherence repair, not a claimed net sorry reduction.

## No longer needed

Remove the public import of
WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality.
Use Sheaf ChartTensorTransport and ChartSummandNaturality for the chart square and
private proof imports of upstream SemilinearTensor and ThreeSquares. The Sheaf
transport and summand lemmas also remain private proof imports. No mathematical
DAG node or source-library declaration is withdrawn. No module is claimed pruned from
the target closure: the upstream implementation remains available to its own consumers.

## Where the brief, the DAG or earlier work was wrong

The assigned repair initially concerned a quarantined zero-hole compatibility
wrapper, which has since been restored to the shared source. It contains no sorry. Re-exporting the upstream theorem alone does not repair the chart cluster:
its upstream SingleTensor import collides with the independent Sheaf SingleTensor
instance declarations. A compile combining the wrapper and Sheaf ChartTensorComponents
reproduced that precise import error. No node is attached directly to this helper module;
the parent chart-homology node already describes this tensor-square argument. Its
attachment, dependencies and unit route remain unchanged.

The let-preserving proof compiled through lcompile.py in 48.5 seconds. The final
module then compiled cleanly without profiling in 58.4 seconds. The final
module imports ChartTensorTransport, which already imports ChartTensorComponents,
so its compile checks the formerly failing combination in a single environment.

The initial delivery compile timed out and pushed nothing. Further profiling
identified monoidal structure normalization; keeping the existing monoidal
structure locally irreducible reduced tactic time to under one second. The
complete profiled file compiled in 52.7 seconds; no proof or file was split.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
