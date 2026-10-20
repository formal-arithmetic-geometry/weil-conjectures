# AlgebraicGeometry.derivedPullback_local_kFlat_model

## Reason

Restore the quarantined module after the upstream derived-pullback unification.
The quarantine error records a declaration collision between the former Sheaf
construction and the adopted source `AlgebraicGeometry.derivedPullback`.
The Sheaf derived-pullback module is now withdrawn and exports no declarations.
Use the adopted source construction and its proved `derivedPullback_spec`.
Explicitly import the existing Sheaf K-flat predicate to preserve the theorem's
signature. Its definition is identical to the source `IsKFlatTensor`; the proof
now records that conversion before applying the source counit clause.

This is an import/API restoration, with no definition or theorem-statement change.
No source-library file changes. The retained theorem is valid for arbitrary
unbounded K-flat models, including the zero complex and the empty-open case.
No target statement or definition used in a target changes in this delivery.

## Old

The archived module's public imports were:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
```

The complete signature of `derivedPullback_local_kFlat_model` is unchanged.
The original proof is retained, with an explicit definitionally equal predicate
conversion. Redundant private imports of Mathlib's ExactFunctor and the source
TensorPullbackAdjunction are removed: the required APIs are already exported by
the remaining imports.

## Users

`tools/downstream.py` reports `unknown module(s)` for this quarantined item.
A source search over both live roots and quarantine finds no live importer and
one archived direct importer (besides the item itself). The item retains its
Lean attachment and all mathematical dependencies. Its unfinished DAG parent
`lem-sc-affine-kflat-residue-pullback-model` remains needed and unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel | R2 | Restored and compiled against the adopted API. |
| Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel | quarantined; not adapted | The theorem name, binders and result are unchanged; no consumer adaptation is forced. |

Other quarantined descendants remain assigned rework items. Restoring this root
does not withdraw any of them or claim to repair their own stale imports.

## Status

landed 20261020T174839-L-808133 2026-10-20 (merge of deliver/R2/Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel)
