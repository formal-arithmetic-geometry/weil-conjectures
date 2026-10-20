# AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction

## Reason

Restore the assigned quarantined Sheaf module after upstream synchronization.
Compiling the archive reproduces the listed missing public changeOfRings and
changeOfRingsHom errors, and additionally the unavailable IsAcyclicTensorKFlat name.
The adopted source already proves the same full theorem. Restore the Sheaf import
path by publicly importing its canonical source implementation, avoiding a duplicate
declaration. The quarantine archive and every source-library file are preserved.

## Old

The archived module publicly imported:

```lean
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
```

Its theorem signature, verbatim:

```lean
theorem derivedModulePullback_adjunction
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y) :
    ∃ (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
      (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
        P.obj M = SheafOfModules.changeOfRings.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
      (_ : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
        P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
          (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
          eqToHom (h N).symm)
      (_ : P.Additive),
      ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (ε : DerivedCategory.Qh ⋙ L ⟶
          P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        L.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
            (ComplexShape.up ℤ)) ∧
        (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
          K.IsAcyclicTensorKFlat → IsIso
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
        Nonempty (L ⊣ derivedModuleDirectImage g)
```

## New

The restored module publicly imports:

```lean
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
```

That canonical module provides the same declaration name with this signature:

```lean
theorem derivedModulePullback_adjunction
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y) :
    ∃ (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
      (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
        P.obj M = SheafOfModules.changeOfRings.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
      (_ : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
        P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
          (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
          eqToHom (h N).symm)
      (_ : P.Additive),
      ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (ε : DerivedCategory.Qh ⋙ L ⟶
          P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        L.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
            (ComplexShape.up ℤ)) ∧
        (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
          K.IsKFlatTensor → IsIso
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
        Nonempty (L ⊣ derivedModuleDirectImage g)
```

IsKFlatTensor has exactly the body of the archived IsAcyclicTensorKFlat definition:
for every acyclic F, the total tensor complex of F and K is acyclic, using the same
SheafOfModules.monoidalCategory. A compile probe reconstructs that body and the full
archived signature and closes it by `exact derivedModulePullback_adjunction g`.
It imports only the restored Sheaf path. Thus the universes, tensor object and map
formulas, left derived universal property, K-flat comparison and adjunction all
remain available with definitionally equal meaning. The theorem's axiom check
reports only propext, Classical.choice and Quot.sound.

The DAG node attaches to the canonical source declaration and quotes its actual
signature. Its proof and all four proof dependencies are retained: the adopted
proof still combines concrete underived tensor pullback, its absolute left derived
comparison, the K-injective direct image and Mathlib's derived-adjunction theorem.
No mathematical dependency or unit step is pruned, and no target statement or
definition changes. No target statement review is reopened.

## Users

The prescribed downstream.py --allow-missing --uses check finds zero live importers
or users of the Sheaf module. A textual import/use search of lean/Sheaf and
quarantine/Sheaf finds only the archived item itself. The adopted source's four
current importers already use the canonical source module and need no adaptation.
The DAG citers below keep their dependencies and declaration names. Claim records
showed them unclaimed; no consumer source is edited.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | unclaimed | Same full theorem and dependency; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh | unclaimed | Same full theorem and dependency; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Same full theorem and dependency; no adaptation. |
| WeilConjectures.AlgebraicGeometry.DerivedInternalHomPullbackMateSections | unclaimed | Same full theorem and dependency; no adaptation. |
| WeilConjectures.AlgebraicGeometry.DerivedDirectImageInternalHom | unclaimed | Same full theorem and dependency; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unclaimed | Same full theorem and dependency; no adaptation. |
| WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction | unclaimed | Same full theorem and dependency; no adaptation. |

The source importers are AffineAlgebraDerivedAdjunctionQCoh,
AffineAlgebraDerivedAdjunctionIsos, FiniteAffineDerivedEquivalence and
DerivedPullbackAcrossUniversesMonoidalAdjunction, all under
WeilConjectures.AlgebraicGeometry. Their source module and theorem are untouched.

## Status

landed 20261020T211803-L-3502078 2026-10-20 (merge of deliver/N2/Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral)
