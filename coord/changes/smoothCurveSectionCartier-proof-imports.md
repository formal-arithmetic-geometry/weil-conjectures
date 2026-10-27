# AlgebraicGeometry.smoothCurveSection_cartier

## Reason

The finite-locally-free Cartier criterion is used only in the proof. The theorem's
statement needs closed immersions, separatedness, smooth relative dimension, and
invertible ideals. Remove the unused FiberDegree import and make
RelativeEffectiveCartier a proof import. The declaration's signature is unchanged.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
```

## Users

`tools/downstream.py Sheaf.TraceFormula.SmoothCurveSectionCartier --uses
AlgebraicGeometry.smoothCurveSection_cartier` reports one downstream module and
no external textual uses of the theorem's name. The existing consumer already
imports the notions appearing in its own statement independently.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.SmoothCurveSectionCartier | G1 | The theorem is proved; signature unchanged. |
| Sheaf.TraceFormula.ValuationNodalPolarSection | unclaimed | Existing source compiled unchanged against the new imports; no adaptation. |

No definition or target statement changes.

## Status

landed 20261023T102738-L-2965414 2026-10-23 (merge of deliver/G1/Sheaf.TraceFormula.SmoothCurveSectionCartier)
