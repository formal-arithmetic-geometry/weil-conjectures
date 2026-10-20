# AlgebraicGeometry.SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison

## Reason

The assigned module is quarantined in coord/rework.tsv after sync 5f7b33eac.
Compiling its archived source reproduces the recorded import error: the environment
already contains ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst from the
Sheaf copy when the upstream model is imported. Its public statement dependency
uses the old K-flat and derived-pullback definitions, whereas its proof dependencies
already use the adopted upstream definitions.

The adopted upstream twin already proves the same theorem. Its public theorem
signature is textually identical to the archived signature. Use that theorem as
the unique implementation and restore the historical module path as a public
re-export. This is an import-environment repair, with zero original local holes.
The upstream implementation and every upstream public import remain untouched.

## Old

The quarantined module publicly imports
Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition and privately imports
Sheaf.Algebra.Homology.KFlatResolution,
WeilConjectures.AlgebraicGeometry.LocalizedComparisonQuasiIsoSquare, and
WeilConjectures.AlgebraicGeometry.StalkComparisonCoordinateInvariance. It redeclares:

```lean
theorem counit_stalkCondition_of_localizedComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (h : ∀ z : X',
      letI := leftAlgebra f g' z
      letI := rightAlgebra f f' g g' sq z
      letI := (tensorMap f f' g g' sq z).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
      ∀ i : ℤ, IsIso ((cohomologyModel f f' g g' sq z G).localizedComparison i)) :
    StalkCondition f f' g g' sq (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj G))
      ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj G))
```

Its private resolution_counit_isIso helper uses IsAcyclicTensorKFlat, while the
upstream helper uses the upstream name IsKFlatTensor.

## New

```lean
module
public import WeilConjectures.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison
```

The same fully qualified public theorem, with the signature above, is provided by
that upstream module. The DAG node's lean record points to the upstream declaration
and file with existing=true; its mathematical statement, proof plan and dependencies
are preserved. The restored module contains no declarations or holes of its own.
It is not an empty withdrawal stub: importing it exposes the original theorem.

A scratch theorem with the entire archived public signature compiles by applying
this re-exported theorem with f, f', g, g', sq, G and h unchanged. The upstream
proof constructs K-flat resolution coordinates, uses the localized quasi-isomorphism
square, then applies coordinate invariance, exactly as in the existing DAG plan.
The axiom check of the re-exported theorem prints only propext, Classical.choice
and Quot.sound. No target statement is edited. No new hypothesis, boundedness,
flatness, nonemptiness or nonzero-ring assumption is introduced; arbitrary complexes
and the vacuous empty-space stalk condition remain covered.

## Users

The source-only downstream.py query with --allow-missing and --uses finds zero
live importers or users: the item and its two immediate consumers are quarantined.
A separate search of quarantine/Sheaf and dag/nodes identifies both still-needed
parents below. Their nodes and dependencies are retained. Their independent sync
repairs are not folded into this item, and no claim that the parents are repaired
is made. Restoring a re-export introduces no new declaration into either parent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison | G4 | Restore the historical import path, re-export the canonical theorem and repoint the node. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Quarantined parent and theorem user; theorem name and call arguments retained; no file changed. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono | unclaimed | Quarantined parent and theorem user; theorem name and call arguments retained; no file changed. |

The unchanged source parent
WeilConjectures.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex already
imports the canonical theorem's module. It is unaffected by the restored shim.


The two archived consumers were also compiled as unchanged scratch files.
RelativelyFlatDerivedBaseChangeComplex fails importing the two derivedPullback
copies; StandardFlatSingleBaseChangeMono fails importing the two
BaseDerivedTensorCohomologyModel copies. These are independent quarantined-parent
repairs, not successful consumer checks. A further compiled-cache check imports
the upstream RelativelyFlatDerivedBaseChangeComplex alone successfully, but loading
that cached parent together with the restored shim exposes a derivedPullback
Sheaf/upstream clash. Its current source imports the upstream theorem already;
the published cached parent's wider definition environment is not coherent with
the canonical module loaded separately. No live source imports the restored shim,
and this packet does not claim to repair either parent's wider environment.
The standalone shim and full-signature application do compile successfully.

## Status

landed 20261020T151218-L-2647831 2026-10-20 (merge of deliver/G4/Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison)
