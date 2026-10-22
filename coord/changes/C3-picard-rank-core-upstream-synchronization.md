# AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank

## Reason

Restore the quarantined item in coord/rework.tsv with zero existing holes. Compiling
its unchanged archive fails at the call to the retired identifier
`picardUniversalRankMatch_of_singleRankMatch`. The former Sheaf conjunction module
is now withdrawn; its DAG node records the stronger, proved upstream synchronization
theorem. Use that recorded theorem directly. The original two-locus fibre-product
construction and all three existing declaration signatures and bodies of definitions
are preserved. The compatibility theorem remains proved by reflexivity.

## Old

Archived proof import and theorem application, verbatim:

```lean
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction
```

```lean
      exact picardUniversalRankMatch_of_singleRankMatch f hO E g hE hd
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatchSynchronization
```

```lean
      exact picardUniversalRankMatch_of_singleRankMatch_without_unit f E g hE hd
```

The new theorem proves the identical conclusion from the same two single-rank
conditions without using hO. The outer theorem retains hO, which is still used in
constructing each single-image locus. The new import is proof-only. All public
imports, the core-condition abbreviation, and both theorem signatures are unchanged.
No source-library module or target is edited and no target interpretation changes.
The rank node retains its Lean attachment and both proof dependencies; its proof
text identifies the current theorem implementing conjunction.

## Users

The standard downstream.py query cannot inspect the absent item as a live module;
with --allow-missing it finds no live consumers. A reverse-import traversal over
both lean/ and quarantine/, preferring live sources, finds 18 consumers. The
only direct consumer is the archived PicardUniversalRankMatchLocusCore; its
unchanged source is compiled against the restored module as a consumer check.
No consumer file is delivered or adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive consumer; public interface and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Archived direct consumer; original source compiles against restored item unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | C3 | Restored with upstream proof import and synchronization call; public interface unchanged. |

## Status

landed 20261022T013351-L-3553638 2026-10-22 (merge of deliver/C3/Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank)
