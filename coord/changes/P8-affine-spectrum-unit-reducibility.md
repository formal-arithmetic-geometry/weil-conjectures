# AlgebraicGeometry.affineSpectrum_unit_normalization

## Reason

The quarantined module fails on a redundant local irreducibility attribute for
`derivedPullback`, now an upstream `irreducible_def`. The adopted upstream twin
already proves the exact same normalization theorem by the exact same coherence
argument. Reuse that complete proof, retain the former Sheaf import path as a
forwarding module, and attach the node to the existing upstream declaration.
This also eliminates the duplicate declaration and its repeated elaboration.
No source-library file, signature, attribute, import or definition is changed.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
```

The quarantined module additionally contains a duplicate complete proof of
`AlgebraicGeometry.affineSpectrum_unit_normalization`, with the redundant line
`attribute [local irreducible] derivedPullback`.
The node's `lean.module` and `lean.file` point to this quarantined Sheaf module.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumUnitNormalization
```

The module forwards to the existing proved upstream declaration. Its public type
is exactly the old type, including universes, instances, chosen comparisons and
conclusion. The node's Lean attachment points to
`WeilConjectures.AlgebraicGeometry.AffineSpectrumUnitNormalization`, with
`existing: true`; the declaration, statement, proof and dependencies are retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization | P8 | Restored as a forwarding module; exact theorem supplied by upstream. |

The quarantined module is absent from lean/Sheaf; no current Lean source imports
it. `tools/downstream.py` reports it as unknown, and source searches find no
current importer. No consumer adaptation is required. The upstream normalization
module and all its consumers remain untouched. Its public import already exposes
the former coordinate-module import transitively. No target statement or
definition changes, and the original unit route remains fully realized.

## Status

landed 20261020T155434-L-3242299 2026-10-20 (merge of deliver/P8/Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization)

Returned landing `5d43e3d54b` rebased through the delivery tool onto freshly
fetched `sheaf-dag`; dry run `62028e63700` compiled and passed server preflight.
The forwarding module independently compiled in 1.3 seconds, and a fresh axiom
check of the upstream normalization theorem printed only `propext`,
`Classical.choice` and `Quot.sound` (2.1 seconds).
