# AlgebraicGeometry.Scheme.finiteFreeResidueModel_pullback: canonical upstream imports

## Reason

Restore the assigned quarantined module from
quarantine/Sheaf/AlgebraicGeometry/FiniteFreeResidueModelPullback.lean.
The coord/rework.tsv row records an import collision between the former Sheaf
and adopted WeilConjectures definitions of AlgebraicGeometry.derivedPullback.
The live Sheaf derived-pullback module is now empty. Use the adopted source
construction explicitly, and use its IsKFlatTensor API throughout the private
K-flat counit helper. Select the upstream K-flat resolution and bounded-flat
criterion, which supply that predicate. This repairs the import environment
and private proof interface; it is not a rebase or an empty restoration.

The public theorem signature, all proof bodies, and the three-step argument
are unchanged from the archive. No definition, target statement, source-library
file, or quarantine archive is changed. The previously reviewed canonical
source derivedPullback is used; this packet defines no competing construction.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
```

The private helper had the following complete signature:

```lean
private theorem pullback_Q_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) P) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P))
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
```

The private helper now has the following signature:

```lean
private theorem pullback_Q_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P))
```

All other imports retain their visibility. The smaller module-sheaf API import
supplies overEquivFunctorObjUnitIso and pullbackFreeIso without importing
quasi-coherent kernels. Every proof body is byte-for-byte the archived proof.
The node retains its attachment, statement, proof steps and dependency IDs;
only proof_origin records the restoration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback | T2 | Restored with canonical upstream imports and private K-flat predicate. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | unclaimed locally; quarantined | Sole direct importer and theorem user. Public theorem signature unchanged; no adaptation forced. |

The source search covered lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf,
including both theorem and module names. A DAG parent search found only
lem-sc-perfect-universal-lowest-zero-model. tools/downstream.py reports the
item as unknown because it is quarantined; the explicit searches include the
archived consumer that the tool consequently cannot enumerate.

An attempted compile of the unchanged archived consumer stops at its imports:

```text
error: import Sheaf.AlgebraicGeometry.PerfectComplex failed, environment already
contains 'AlgebraicGeometry.Scheme.IsPerfect' from
WeilConjectures.AlgebraicGeometry.PerfectComplex
```

That separate quarantine failure is not caused by this packet. No consumer edit
is needed for this theorem's unchanged arguments and conclusion. An independent
probe states the archived public signature verbatim and applies the restored
theorem with exactly those arguments; it compiles. The item compiles in 14.4 s,
and its theorem's axioms are exactly propext, Classical.choice and Quot.sound.
There are zero direct holes before and after this repair.

## Status

landed 20261020T174851-L-812584 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback)
