## What changed

Restored Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents from
quarantine. Replaced the mixed upstream/Sheaf chart-tail import chain with proved
private lemmas for single-factor tensor components, naturality, and the degree-zero
single-complex comparison. The chart proof combines these formulas with the
extension comparison. Both public statements are textually identical to quarantine.
The four local tensor instances reuse the identical chart-model instances.
Local transparency settings avoid expanding the sheaf tensor structure.
The extension/naturality calculation is now a proved private API over abstract
categories, specialized once at a bundled affine ring. The specialization eliminates
repeated conversions between the ring and its carrier while retaining the entire
calculation in this module. The chart theorem applies that specialization and the
degree-zero single-complex formula.

The sole public import is now QCohTensorResolutionChartTensor, which supplies the
chart comparison occurring in the statements. No upstream file is changed.
The bundled-ring version compiled cleanly against the current server dependencies
in 46.1 seconds. The final packet additionally removes the unused specialized
naturality helper and the unused chart-complex local binding. The delivery compile,
every-declaration axiom probe, and server preflight passed on this complete file
(dry-run commit e33eeb1e920). The delivery is CODEX for independent review because
it restores a returned module and changes public imports and local-instance bodies.

Change record: coord/changes/a8-chart-tensor-components-import-coherence.md.

## Proved and sorry left

This repairs an already proved, quarantined module: 0 original holes, 0 holes
closed, 0 holes added, and 0 holes left. These public declarations have complete
proofs:

- AlgebraicGeometry.tensorResolutionMapExtendIso_inv_f
- AlgebraicGeometry.tensorResolutionChartTensorIso_f

These private helpers are also completely proved:

- AlgebraicGeometry.single₂_inv_f
- AlgebraicGeometry.single₂_inv_map_f
- AlgebraicGeometry.tensor_single_tail
- AlgebraicGeometry.tildeTensorRightIso_hom_app
- AlgebraicGeometry.map_extend_tensor_component
- AlgebraicGeometry.tilde_map_extend_tensor_component
- AlgebraicGeometry.single_model_map_f

No decomposition, new public statement, axiom, or postponed proof.

## No longer needed

Removed public imports:

- Sheaf.AlgebraicGeometry.QCohTensorResolutionChartModel: its homology comparison
  is unused; import its chart-tensor dependency directly.
- Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality: the component
  calculation uses naturality of the tensor comparison itself.
- WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorTail: replace
  its specialized calculation with the proved generic tensor_single_tail lemma.

The proof also does not use tensorResolution_single₂_inv_f: the generic
single₂_inv_f follows from the library's first-factor and flip component formulas.
Its module remains a transitive import of the chart-tensor definition.
No upstream declaration or module is removed. No global module pruning is claimed.
No DAG node is attached to the item, and proved private helpers need no new nodes.

## Where the brief, the DAG or earlier work was wrong

Repair of return ae853a6ccc: the landing refused the old base 0dc07eb8c after
an intervening write. Re-read the current checkout, rework row, claim, return,
and quarantine source. The item is currently absent from lean/ and preserved
at quarantine/Sheaf/AlgebraicGeometry/QCohTensorResolutionChartTensorComponents.lean.
Compared both public theorem signatures byte for byte with that current archive:
both are identical. Reapply the complete import-collision repair to this current
source and deliver on the newly fetched base. This restores the assigned module;
it does not withdraw the quarantine, erase its statements, or claim a new proof
hole has been closed.

The first repair dry run exceeded the file limit while appending its axiom probe.
Profiling isolated kernel conversion checking rather than tactic execution: a
diagnostic stopped before the final application spent about 30 seconds checking
its theorem term, versus about two seconds executing the initial rewrites.
The private abstract and bundled-ring APIs above remove the repeated sheaf tensor
normalizations; no file is split and the timeout is unchanged.

Current downstream search again reports no active consumers;
the three quarantined consumers and their component references were rechecked.

The item is absent from lean/: it was quarantined after the upstream sync.
Its original file in quarantine/Sheaf/AlgebraicGeometry/ has zero sorries.
The assigned repair is the import collision with the upstream chart-model chain,
whose second single-tensor module redeclares TensorResolutionSingleTensor_localInst1.

A trial consumer-cluster compile stops at the separate quarantined root
QCohTensorResolutionChartComparisonIso with a duplicate isKFlat_tilde declaration.
The consumers remain quarantined; this packet restores only the assigned root.
The public component statements and their meanings are unchanged.

Searches used msearch.py leanfinder (single-factor tensor component formula),
loogle (CochainComplex.mapBifunctorSingle₂Iso; identifier unknown to the service),
and grep (tensorResolutionChartTensor_tail|mapBifunctorSingle₂Iso_inv_f; no hits).
Direct source search located the existing first-factor, flip, and inclusion
naturality formulas used in the generic proof.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
