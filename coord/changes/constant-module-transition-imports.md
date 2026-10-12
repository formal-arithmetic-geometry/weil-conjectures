# ConstantModuleTransitionCoefficients imports

## Reason

The direct public import of ConcreteCoefficients is redundant: the retained
ConstructibleSheaf.Defs import already exposes the instances needed by the
statement. The complete generator proof also compiles without the direct import.
No additional proof import is needed.

## Old

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

## New

The direct import is removed. The only retained import is:

public import WeilConjectures.ConstructibleSheaf.Defs

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstantModuleSectionCoefficients | N3 | Unchanged statements and proofs; its original file compiled against the delivered module and retained public imports. |

## Status

landed 20261012T194056-L-450760 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ConstantModuleTransitionCoefficients)
