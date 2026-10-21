# AlgebraicGeometry.Scheme.picardRankMatch_derived_truncation_data

## Reason

Restore the assigned rework root from its coord/rework.tsv quarantine archive, with
its entire existing complete proof. The archive fails at statement lines 117, 123,
130, 132 and 140: unknown identifier derivedPullback, with Lean recommending a public
import of WeilConjectures.AlgebraicGeometry.DerivedPullback. The archive instead
publicly imports Sheaf.AlgebraicGeometry.DerivedPullback, now an empty withdrawn module.
Replace that import by the current source module and explicitly qualify the intended
AlgebraicGeometry.derivedPullback.{u, w} throughout. This is exactly the shared-category
functor used by tensorDegreeZeroMateSquare and IsDerivedModuleBaseChangeMap.
All binders, hypotheses, universes, witnesses, canonical maps and conclusions stay.
No definition, target meaning or unit route changes. No source-library file changes.

The two immediate consumers PicardBaseChangeStalkSurjective and PicardRankMatchBaseChange
are restored verbatim from quarantine as part of the assigned rework cluster.
They retain their complete existing proofs and all original signatures/imports.

## Old

Original public import:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

The full original signature from quarantine:

```lean
theorem picardRankMatch_derived_truncation_data
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
    let M := (Modules.pushforward (pullback.snd f g)).obj
      ((Modules.tensorPullback (pullback.fst f g)).obj F)
    ∃ (K : schemeDerivedCategory T)
      (a : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M ⟶ K),
      IsPerfect T K ∧
      (∀ (Y : Scheme.{u}) (k : Y ⟶ T) (i : ℤ), i < 0 →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
            ((derivedPullback k).obj K))) ∧
      (∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ r : ℕ,
        ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((derivedPullback (k ≫ U.ι)).obj K)) r) ∧
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map a) ∧
      ∀ (Y : Scheme.{u}) (k : Y ⟶ T),
        let H := DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
        ∃ (e0 : (Modules.tensorPullback k).obj M ≅
            H.obj ((derivedPullback k).obj ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M)))
          (e1 : H.obj ((derivedPullback k).obj K) ≅
            (Modules.pushforward (pullback.snd (pullback.snd f g) k)).obj
              ((Modules.tensorPullback (pullback.fst (pullback.snd f g) k)).obj
                ((Modules.tensorPullback (pullback.fst f g)).obj F))),
          Modules.moduleBaseChangeMap (pullback.snd f g)
              (pullback.snd (pullback.snd f g) k) k
              (pullback.fst (pullback.snd f g) k) pullback.condition
              ((Modules.tensorPullback (pullback.fst f g)).obj F) ≫ e1.inv =
            e0.hom ≫ H.map ((derivedPullback k).map a)
```

## New

Current public import:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The full restored signature (only qualification changes):

```lean
theorem picardRankMatch_derived_truncation_data
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
    let M := (Modules.pushforward (pullback.snd f g)).obj
      ((Modules.tensorPullback (pullback.fst f g)).obj F)
    ∃ (K : schemeDerivedCategory T)
      (a : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M ⟶ K),
      IsPerfect T K ∧
      (∀ (Y : Scheme.{u}) (k : Y ⟶ T) (i : ℤ), i < 0 →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
            ((AlgebraicGeometry.derivedPullback.{u, w} k).obj K))) ∧
      (∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ r : ℕ,
        ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((AlgebraicGeometry.derivedPullback.{u, w} (k ≫ U.ι)).obj K)) r) ∧
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map a) ∧
      ∀ (Y : Scheme.{u}) (k : Y ⟶ T),
        let H := DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
        ∃ (e0 : (Modules.tensorPullback k).obj M ≅
            H.obj ((AlgebraicGeometry.derivedPullback.{u, w} k).obj ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M)))
          (e1 : H.obj ((AlgebraicGeometry.derivedPullback.{u, w} k).obj K) ≅
            (Modules.pushforward (pullback.snd (pullback.snd f g) k)).obj
              ((Modules.tensorPullback (pullback.fst (pullback.snd f g) k)).obj
                ((Modules.tensorPullback (pullback.fst f g)).obj F))),
          Modules.moduleBaseChangeMap (pullback.snd f g)
              (pullback.snd (pullback.snd f g) k) k
              (pullback.fst (pullback.snd f g) k) pullback.condition
              ((Modules.tensorPullback (pullback.fst f g)).obj F) ≫ e1.inv =
            e0.hom ≫ H.map ((AlgebraicGeometry.derivedPullback.{u, w} k).map a)
```

## Users

The assigned root is absent from lean/, so tools/downstream.py reports unknown module.
A source scan of lean/ and quarantine/ finds one direct declaration caller,
PicardBaseChangeStalkSurjective, and the eighteen downstream quarantined modules below.
The direct caller uses the same arbitrary shared-category universe and the same
specified canonical comparison; its signature and proof are unchanged. The next
consumer, PicardRankMatchBaseChange, is also restored unchanged. Other consumer
statements still mean exactly the same thing and need no adaptation to this root.
Their separate pre-existing dependency/import failures are not changes to this interface.
No target statement is edited and no mathematical definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | P4 cluster | Restore preserved implementation unchanged; test against the repaired root. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed at inspection | Quarantined downstream consumer; original mathematical interface unchanged; not withdrawn. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | P4 cluster | Restore preserved implementation unchanged; test against the repaired root. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | P4 cluster | Restore full zero-hole implementation; fix public derived-pullback import and qualify functor. |

## Status

landed 20261021T233751-L-859085 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData)
