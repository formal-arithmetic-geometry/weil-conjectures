# Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux

## Reason

The module was quarantined by the 2026-10-20 upstream sync because its legacy
Sheaf KFlatPullback import duplicated tensor-pullback declarations already imported
from WeilConjectures. The adopted source now supplies this entire module, including
both public theorems and their resolving-class proofs. Restore the import path as
a public re-export, and attach its two existing DAG nodes to the source declarations.
This repairs the recorded import collision; it does not withdraw the absent file.
The quarantine archive is untouched.

## Old

The archived module publicly imported:

```lean
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
```

It defined `AlgebraicGeometry.RingedSpace.exists_tensorPullback_leftDerived` and
`AlgebraicGeometry.RingedSpace.leftDerived_tensorPullback_absolute`, and three
private helpers. Its full old theorem signatures remain in the quarantine archive
and the base versions of the two delivered DAG nodes.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux
```

The same two public names are supplied by that import. The source signatures use
`CochainComplex.IsKFlatTensor`, whose definition is identical to the old
`CochainComplex.IsAcyclicTensorKFlat`. A compile check reconstructing the old
predicate and both old signatures accepts each source theorem directly with
`exact`, without rewriting, added hypotheses, or changed universes. Both node
attachments now quote the source signatures verbatim and name their source file.
Their mathematical statements, proof plans and dependency lists are unchanged.
All upstream signatures, attributes, imports and proof bodies are untouched.
No target definition or statement changes; no new target review is needed.

## Users

`tools/downstream.py --allow-missing --uses` reports zero live importers. Searching
both lean/ and quarantine/ finds the following archived direct importer and the
four further quarantined consumers named by coord/rework.tsv. None is modified:
restoration of the compatibility path preserves access to the canonical names.
These modules' own sync repairs remain their respective assignments.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute | unclaimed, quarantined | Direct import path restored; same names and definitionally equal K-flat hypothesis. |
| Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral | unclaimed, quarantined | Transitive dependency restored; no statement change. |
| Sheaf.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization | unclaimed, quarantined | Transitive dependency restored; no statement change. |
| Sheaf.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction | unclaimed, quarantined | Transitive dependency restored; no statement change. |
| Sheaf.AlgebraicGeometry.RingedSpacePastedUnitKFlatHom | unclaimed, quarantined | Transitive dependency restored; no statement change. |

## Status

landed 20261020T160756-L-3406582 2026-10-20 (merge of deliver/H1/Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux)
