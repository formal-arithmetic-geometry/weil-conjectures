# AlgebraicGeometry.smooth_toric_saturated_sharp_reduction

## Reason

The item still had the legacy import-only header. Convert it to the required module layout,
expose its existing declarations, retain statement dependencies as public imports, and import
normalization, sharpening exactness and unit splitting privately for the proof. Remove the
unused monoscheme realization, normal decomposition and face sharpening imports. No public
declaration signature or definition body changes.

## Old

```lean
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.TraceFormula.FsFaceSharpening
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.LinearAlgebra.FreeModule.PID
```

The old file has no `module` command or exposed public section.

## New

```lean
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.GroupTheory.IntegralSharpeningGroupExactness
import Mathlib.GroupTheory.MonoidLocalization.Finite
import Sheaf.GroupTheory.FineMonoidUnitSplitting
import Sheaf.RingTheory.AffineMonoidAlgebraNormalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic
```

An `@[expose] public section` follows the unchanged module docstring. Every existing
mathematical declaration retains its signature, and all three definitions retain their bodies.
The five new helpers are private proved theorems used only in the item proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SmoothToricSaturatedSharpReduction | D7 | Required module header and proof dependencies; existing statements and definitions unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.SmoothToricSaturatedSharpReduction --uses
AlgebraicGeometry.toricLaurentAlgebra` reports no downstream modules and only this module as a
textual user. A direct import search across `lean/` also reports no importers. The parent DAG
statements remain attached and this module is retained: zero current importers is not used to
withdraw any mathematics. No target or target definition is changed.

## Status

landed 20261026T081507-L-1983477 2026-10-26 (merge of deliver/D7/Sheaf.AlgebraicGeometry.SmoothToricSaturatedSharpReduction)
