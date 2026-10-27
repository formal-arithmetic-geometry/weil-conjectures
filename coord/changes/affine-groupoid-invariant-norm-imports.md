# AlgebraicGeometry.affineGroupoid_invariant_norm

## Reason

The invariance proof uses the chart formulas in `hn`, so it does not need the norm-chart
existence theorem. Its statement needs the norm definition only. Replace the public construction
import by the public norm-definition import. Remove redundant private imports already supplied by
the necessary modules; add private imports for the proof APIs. The theorem signature and all
existing definitions remain unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
```

## New

```lean
public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import Mathlib.RingTheory.Norm.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm --uses
 affineGroupoid_invariant_norm` finds the following 15 downstream modules. No downstream source
currently mentions the theorem by name; both direct consumers have unfinished proofs and keep
their own norm-chart imports. They therefore retain every declaration they previously received
from that module. No statement or definition changes meaning, and no target review is reopened.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres` | unclaimed | Direct importer already imports norm-chart module; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant` | B7 | Direct importer already imports norm-chart module; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood` | J1 | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.EquivariantMarkedPlurinodalFieldAlteration` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteQuotientGenericFields` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse` | S9 | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` | unclaimed | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable` | W8 | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.Paper.NormalLatticeFiniteCoverPresentation` | M6 | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |
| `Sheaf.SecPurity.NormalLocallyConstantFiniteSection` | S8 | Transitive consumer; norm-chart import retained by both direct consumers; no adaptation. |

## Status

landed 20261023T131938-L-2174959 2026-10-23 (merge of deliver/U2/Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm)
