# AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank

## Reason

The assigned rework row preserves an archived zero-hole module whose old proof called the
retired single-rank conjunction declaration. The current shared source already contains
C3's landed upstream-synchronization repair and compiles. This delivery makes a further
substantive pruning: reuse the existing locally finitely presented rank-match construction
instead of reconstructing the same intersection through a separate single-rank branch.
The stronger construction has the identical universal predicate, assumes no hO, and also
provides local finite presentation. Forgetting that extra property proves the old statement.
No definition, signature, public import, instance, source-library file or target changes.
The abbreviation PicardUniversalRankMatchCoreCondition retains its original body verbatim.

## Old

Private proof imports:

```lean
import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus
import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatchSynchronization
```

The proof constructs two single-image loci, takes their categorical pullback, and proves
its factorization property using the upstream synchronization theorem.

## New

```lean
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore
```

```lean
  have _ := @hO
  obtain ⟨W, j, hj, _, hW⟩ := exists_picardUniversalRankMatchLocus_finitePresentation_core f E
  exact ⟨W, j, hj, fun g ↦ hW g⟩
```

The retained hO binder belongs to the unchanged interface. The stronger theorem already
constructs the actual intersection and handles rank zero, empty schemes, and mixed-rank
fibres. This is reuse of an existing proved theorem, with no new existence assertion or hole.
The compatibility theorem remains rfl. The DAG now records the stronger construction as
its sole proof dependency. The blueprint unit's realized lists are empty, and both results
belong to the same unit; no unit step or statement is bypassed.

## Users

The ordinary downstream query sees no live consumers, since the parents are quarantined.
A reverse-import traversal of lean/Sheaf, lean/WeilConjectures, and the corresponding
quarantine roots, preferring live files over archives, finds the following 18 consumers.
The unchanged archived direct consumer PicardUniversalRankMatchLocusCore was compiled
with the changed item in import order. No consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | not queried; not edited | Identical public declarations and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | not queried; not edited | Identical public declarations and meaning; no adaptation. |

## Status

landed 20261022T020055-L-4194105 2026-10-22 (merge of deliver/B2/Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank)
