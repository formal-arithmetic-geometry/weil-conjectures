# affineSpectrum_counit_square K-flat import restoration

## Reason

Restore the module quarantined by the 2026-10-20 upstream sync. Its archived statement
uses `CochainComplex.IsAcyclicTensorKFlat`, but its upstream public imports now use
`IsKFlatTensor` and no longer expose that project predicate. The recorded compiler
error is `Invalid field IsAcyclicTensorKFlat` at the hypothesis `hP`.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare
```

The archived theorem signature, proof, attributes, and documentation are unchanged.
The import supplies the existing predicate used by the statement; no definition,
mathematical hypothesis, conclusion, or target changes. No upstream file is modified.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare | N3 | Restored; compiles. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | unclaimed, quarantined | Sole archived direct importer and caller; unchanged theorem and predicate. |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport | unclaimed, quarantined | Archived transitive importer; unchanged mathematical interface. |

The live source has no importer of the missing module. The source-only downstream
check therefore requires `--allow-missing`. Searching both live and quarantined
sources finds the direct caller above, which still passes its original `hP` to
the restored theorem. The DAG parent `lem-pc-affine-spectrum-canonical-comparison-square`
and the item's Lean attachment and dependencies are preserved. Other quarantined
modules remain available for their own rework assignments; none is withdrawn.

## Status

landed 20261020T145533-L-2408717 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare)
