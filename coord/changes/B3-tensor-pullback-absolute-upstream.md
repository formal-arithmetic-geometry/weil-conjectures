# Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute

## Reason

Restore the quarantined module after the upstream sync. Its archived public imports
no longer expose changeOfRings or changeOfRingsHom, and KFlatPullback has been
withdrawn, so IsAcyclicTensorKFlat is also unavailable. These failures are reproduced
with lcompile.py. The adopted source already supplies the same public theorem and
its complete two-line assembly of the derived comparison and absoluteness lemmas.
Re-export that canonical module instead of redeclaring its theorem. The quarantine
archive is preserved. No source-library file is edited.

## Old

Archived direct imports:

```lean
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux
```

Archived signature, verbatim:

```lean
theorem exists_absolute_leftDerived_tensorModulePullback
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
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
      ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
        (L ⋙ H).IsLeftDerivedFunctor
          ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
            (ComplexShape.up ℤ))
```

## New

The restored compatibility module publicly imports:

```lean
public import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
```

The imported canonical theorem has the following signature, verbatim:

```lean
theorem exists_absolute_leftDerived_tensorModulePullback
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
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
      ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
        (L ⋙ H).IsLeftDerivedFunctor
          ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
            (ComplexShape.up ℤ))
```

Only the spelling of the K-flat predicate changes: IsKFlatTensor and the archived
IsAcyclicTensorKFlat both mean acyclicity of F tensor K for every acyclic F, with
the same monoidal structure. A compile probe reconstructs the archived predicate
body and full archived theorem type and supplies it directly by the canonical
theorem. No rewriting, hypotheses or universe changes are needed. Axiom checking
of the canonical theorem reports only propext, Classical.choice and Quot.sound.

The existing node now attaches to the source declaration and its quoted signature.
Its proof and proof_deps explicitly describe the two auxiliary results that the
source proof combines. The former direct proof dependencies remain below those
auxiliary nodes; no mathematical branch or unit step is withdrawn. No target
statement or definition changes, so no target statement review is reopened.

## Users

The prescribed downstream.py --allow-missing --uses check reports zero live
importers. An import-graph check including quarantine finds the four consumers
below. Their archived uses retain the same theorem name and definitionally equal
K-flat hypothesis; their independent sync repairs are not part of this delivery.
The last two rows are additional DAG parents whose dependency remains valid.
No consumer requires adaptation, and no deleted.txt is supplied.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral | unclaimed, quarantined | Direct import restored; its application at line 94 has the same full type. |
| Sheaf.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction | unclaimed, quarantined | Direct import restored; applications at lines 185 and 187 retain both derived comparisons. |
| Sheaf.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization | unclaimed, quarantined | Transitive import restored; same interface. |
| Sheaf.AlgebraicGeometry.RingedSpacePastedUnitKFlatHom | unclaimed, quarantined | Transitive import restored; same interface. |
| Sheaf.Paper.ModuleCupGlobalTensorPullback | unclaimed | DAG parent remains valid; no live import of this module or use of its theorem. |
| Sheaf.Paper.GlobalTensorPullbackDerivedData | unclaimed | DAG parent remains valid; no live import of this module or use of its theorem. |

## Status

landed 20261020T164440-L-3930427 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute)
