# etaleCtfChartDomain public imports

## Reason

The completed proof uses the ordinary exact-monoidal Tor comparison and the separately
stated scalar, compact-support and pullback/twist models. The coefficient-sized comparison
and cochain change-of-rings imports are redundant; the public signature only needs the
actual finite Tate construction. Remove these redundant reexports while preserving every
public declaration, signature, definition body and instance.

## Old

```lean
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
```

## New

```lean
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ChartCounitScalarTransport | M9 | Original compiled against reduced reexports; no edits. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | H3 | Original compiled against reduced reexports; no edits. |
| Sheaf.Paper.AffineCounitScalar | E1 | Original compiled against reduced reexports; no edits. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | W6 | Transitive consumer compiled against reduced reexports; no edits. |

Additional consumers present on the resumed source snapshot:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Current original compiled against the item; no edits. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | K7 | Current original compiled against the item; no edits. |

The six users together are the current complete downstream.py module list. No mathematical definition used by a
target changes, so this does not reopen a target's statement review. Consumer copies are
compiled unchanged and are omitted from the delivery after checking.

## Status

landed 20261025T013154-L-3936496 2026-10-25 (merge of deliver/E2/Sheaf.Paper.EtaleCtfChartDomain)
