## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_integralClass_pullback`
by a proof from ordinary site-comparison endpoint identities. The geometric step uses the
existing proved `Scheme.gmCohomologyMap_toCohomologicalPicardGroup`, including the
identification of the pulled-back Picard representative. Exact-functor Ext compatibility
then transports the ordinary sheaf square through constant towers, with the original
single and shift comparisons.

The nine original constructions, from `abPull` through `unitsDerivedPull`, have been moved
to the new public module `Sheaf.Paper.TowerIntegralPullbackData`. Their signatures and
bodies are unchanged; the assigned module publicly imports them. The new module also
proves the componentwise endpoint comparisons and the chartwise adjoint formula for units.
No adopted source-library module or other existing Lean module is changed.

The proved realization and square interfaces name the canonical derived comparison maps
with their objectwise source types. This avoids repeated conversion between composed
functors and their objectwise action when specializing to integer sheaves. All new data
are explicit constructions. No auxiliary normalization holes are left.

The transport theorem compiles in 58.3 seconds, its geometric square in 52.5 seconds,
and the assigned module in 8.7 seconds. Compilation and delivery checks are recorded by
the delivery tool. The two direct
consumers of the assigned module are checked against the relocated public constructions.

## Proved and sorry left

Original holes: 1. Closed:
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_integralClass_pullback`
(node `lem-sp-tower-integral-class-pullback`). The assigned module has zero holes.

Added: 1:
`AlgebraicGeometry.ProEtale.SpTowerClasses.integral_site_pullback_endpoints`
(node `lem-sp-integral-site-pullback-endpoints`). This is the conjunction of the ordinary
integer and full-units endpoint squares across the etale-to-pro-etale comparison. It has
no line bundle, cohomology class, derived-category morphism or tower. Its docstring gives
the source and the proof by transposing through the adjunctions and checking chart maps.

This is a decomposition: one original hole is replaced by one strictly smaller new hole.
The Ext, Picard and constant-tower composition steps are proved. No `sorry` occurs in a
definition or a private declaration. The delivery tool computes the closure-wide totals.

## No longer needed

No module is withdrawn. All original public imports remain available. The private
functor-category limits import moves with the constructions to `TowerIntegralPullbackData`.

The proof does not directly need the originally planned modules
`Sheaf.CategoryTheory.ExtOneExtensionClassification`,
`WeilConjectures.CategoryTheory.Sites.Torsor`,
`WeilConjectures.AlgebraicGeometry.Sites.GmPicard`, or
`Sheaf.Paper.SmoothPurityTowerClasses` to reconstruct an integral extension.
The corresponding planned nodes `lem-weil-pbc-ext-one-extension-classification`,
`lem-sc-torsor-h1`, `lem-sc-line-bundle-torsor`, and `det-sp-tower-classes`
are replaced in the assigned node's proof dependencies by the existing Picard naturality
and the explicit transport steps. The planned `lem-weil-pbc-complex-ses-triangle` and
`lem-weil-pbc-exact-functor-ses-triangle-image` routes are also unnecessary for this proof.
These declarations may remain necessary transitively or for other consumers; none is
removed, weakened or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The original plan reconstructs frame torsors and integral extensions after pullback.
The source library already proves the required Picard naturality for arbitrary scheme
morphisms. The remaining geometric compatibility is the pair of ordinary integer and
units endpoint identities in the site-comparison square.

The new endpoint statement has been checked on empty schemes, trivial units and arbitrary
nonflat maps. It does not assert that the units comparison is invertible. Its site-square
orientation is `f_proet^* nu_Y^*` to `nu_X^* f_et^*`.

The assigned source is present and retained. No quarantined path is withdrawn. The public
constructions are moved only to permit the proof interfaces to depend on them without an
import cycle. Their original bodies were compared after removing comments and whitespace.
The 60-second limit is unchanged; no shared definition or instance is modified.

## New nodes

`lem-sp-integral-site-pullback-endpoints` records the sole remaining obligation, in
`Sheaf.Paper.IntegralSitePullbackEndpoints`.

`lem-sp-integral-cohomology-site-pullback` records the proved transport of an arbitrary
integral units cohomology class across the site square, in
`Sheaf.Paper.IntegralCohomologySitePullback`.

`lem-sp-line-bundle-proetale-class-pullback` combines that transport with existing Picard
naturality, in `Sheaf.Paper.LineBundleProEtaleClassPullback`.

`lem-sp-constant-tower-derived-square` records exact-derived transport through constant
towers, including the canonical endpoint composites, in
`Sheaf.Paper.ConstantTowerDerivedSquare`.

`def-sp-tower-integral-pullback-data` owns the relocated original constructions and their
proved ordinary endpoint API, in `Sheaf.Paper.TowerIntegralPullbackData`.

`def-sp-integral-tower-realization-data` records explicit class realizations, the derived
boundary morphism types and their canonical maps, in
`Sheaf.Paper.IntegralTowerRealizationData`.

`def-sp-integral-tower-pullback-square-data` records the normalized square data, in
`Sheaf.Paper.IntegralTowerPullbackSquareData`. Separating its declaration keeps each file
within the unchanged compilation limit.

`lem-sp-integral-tower-pullback-square` records the proved normalized square interface,
in `Sheaf.Paper.IntegralTowerPullbackSquare`.

`def-sp-line-bundle-tower-pullback-square` records the explicit square constructed from
a line bundle and its geometric pullback, in `Sheaf.Paper.LineBundleTowerPullbackSquare`.

Each node file is under `dag/nodes/sec-smooth-purity/`. The assigned node's statement is
unchanged; its Lean attachments and proof dependencies follow the new module organization.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ConstantTowerDerivedSquare": "1219fda5912cddc1e72c55ca9e5a7ec7d677ed14", "Sheaf.Paper.IntegralCohomologySitePullback": "294725355d39d8b3c3d55524b1a42d5c6d8c8653", "Sheaf.Paper.IntegralSitePullbackEndpoints": "9e005da89e22d2b1b7ea199baa6b475d2e0356e4", "Sheaf.Paper.IntegralTowerPullbackSquare": "7651c3bf293fa207cdffe06370308e71e1d8976f", "Sheaf.Paper.IntegralTowerPullbackSquareData": "bbaff9c885c83be0588f78796c8dd32470afe9af", "Sheaf.Paper.IntegralTowerRealizationData": "4fbae875da3028fedfbadce24c130eb9e2c187cd", "Sheaf.Paper.LineBundleProEtaleClassPullback": "c4a4c35874d158a2b96254687eb7c778ba967950", "Sheaf.Paper.LineBundleTowerPullbackSquare": "251e40185dfbdb2457792cb75417ef67a1518319", "Sheaf.Paper.TowerIntegralClassPullback": "d961ad3f88446f2e8b8965572e9e7353430bc8c1", "Sheaf.Paper.TowerIntegralPullbackData": "cca0f94d1c46a6b88a663c5791647daf61c66dcf"}, "results": {"Sheaf.Paper.TowerChernPullbackData": {"hash": "c5311d43f3d5fbb94594965dfbd55d394ece11c0", "status": "OK"}, "Sheaf.Paper.TowerChernRealizationPullback": {"hash": "e36a94c84b8488921b94186dd797a565ced6ab92", "status": "OK"}}, "seconds": 249, "time": "2026-10-28T00:21:26+0800", "transitive": 0, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
