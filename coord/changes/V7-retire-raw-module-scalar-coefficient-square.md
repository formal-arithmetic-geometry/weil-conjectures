# Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare

## Reason

Complete the explicit retirement assignment in coord/retire-items.tsv against
its current source. The item is now a compatibility module with no declarations:
it publicly imports the already proved canonical coefficient square and the
historical derived-comparison API. The original six consumers no longer import
this module. Retaining the wrapper leaves a stale retirement item and an unused
public import edge to the derived-comparison API.

The canonical replacement is the existing
WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare. Its
rawModuleScalar_coefficient_square_of_unshifted applies the private generic
shift_square to the already proved unshifted coefficient identity and its
CommShift theorem, using the existing kernel-checked structural congruence
helper. rawModuleScalar_coefficient_square applies that theorem. No additional
proof obligation, replacement axiom, definition or data choice is introduced.

The live source already contains the integrated factor construction:
moduleCoefficientFactor uses higherDirectImageRawOverCoefficient in
WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors. The scalar
factor remains in the adopted coefficient-square module. No adopted source
signature, attribute, public import, definition body or proof is changed.

The square and shift-transport nodes already attach to their canonical upstream
module. All seven current DAG parent references use these retained nodes;
none attaches to the withdrawn Sheaf module. Neither node realizes a unit
statement or proof step. Historical mentions of the item in node provenance are
retained. Thus the retirement does not depend merely on zero Lean importers:
the explicit reviewed retirement request, the actual replacement proofs and
all current parent attachments agree. No target meaning or unit route changes.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The canonical shifted coefficient square and the historical comparison API.
The reverse comparison is the inverse of the canonical forward comparison.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/

@[expose] public section
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/RawModuleScalarCoefficientSquare.lean
through deleted.txt. The delivery tool writes the standard empty module:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

No declarations are removed: the old module had none. The square declarations,
scalar factor and historical comparison API remain at their existing canonical
locations. DAG metadata is already correct and requires no edits.

## Users

`python3 tools/downstream.py
Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare --uses
rawModuleScalar_coefficient_square` reports zero downstream modules and zero
users. A separate full-text scan of lean/Sheaf, lean/WeilConjectures and
quarantine also finds zero importers. The six consumers listed by the historical
retirement row were individually checked against the current source:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | V7 | Withdraw the unused, declaration-free wrapper. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Already withdrawn; no importer to adapt. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Already withdrawn; no importer to adapt. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Already withdrawn; no importer to adapt. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Already withdrawn; no importer to adapt. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Imports canonical factors directly; no change. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Imports the canonical native-factor API and abelian formula; no change. |

The live canonical parents RawModuleAbelianHomTargetFormula,
RawModuleScalarHomCompositeFormula, RawModuleScalarHomEvaluation,
RawModuleAbelianHomMapNaturality, RawModuleAbelianHomSourceFormula and
RawModuleScalarPullbackModuleFormula retain their existing upstream square
imports and DAG dependencies. The square node retains its dependency on the
upstream shift-transport theorem. No consumer requires adaptation.

## Status

landed 20261025T101700-L-3721585 2026-10-25 (merge of deliver/V7/Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare)
