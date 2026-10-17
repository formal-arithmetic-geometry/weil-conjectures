# PerfectDirectImageBaseChange final withdrawal

## Reason

The previous B3 retirement landed during this worker's initial read. It removed the combined
public theorem and adapted its actual callers, but kept a compatibility module with four
public imports. Its only remaining importers are PicardSingleRankPerfectChart and
SmoothCurveEtaleStructureDirectImages, both with proof-only imports and neither using any
of its declarations (it has none). Remove these two redundant imports and withdraw the
now-unreachable item under the worker brief, step 8d. This completes the duplicate retirement
with actual module pruning, rather than resubmitting the already landed repair.

No declaration signature, visibility, definition body, theorem proof, target or mathematical
statement changes. The source theorem remains available in its original source module;
SmoothCurveEtaleStructureDirectImages already imports that source module directly.
PicardSingleRankPerfectChart obtains its perfect chart from ProperFlatDirectImagePerfectChart.
The item node keeps its source attachment and existing derived caller reduction, with its
re-export note corrected to reflect withdrawal. There is no new mathematical route.

## Old

The item's entire existing module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups F1 and H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange

/-! # Retired perfect direct image compatibility module

The blueprint node `lem-pc-rf-perfect-base-change` is recorded at
`AlgebraicGeometry.Scheme.Modules.perfect_and_baseChange_cechModuleComplex_of_isProper`.
This module re-exports its source module. Former derived-category users now use
`properFlat_single_derivedDirectImage_perfect` for perfectness and the canonical
relatively flat module base-change API for the particular comparison they need.
The source theorem's Cech statement is not identified with the stronger retired statement.
-/

@[expose] public section
```

Each direct user also contains this proof-only import:

```lean
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
```

## New

The item is listed in deleted.txt as prescribed by step 8d. The delivery tool lands:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The two direct importers omit the quoted import. Every other byte of both consumer modules,
including all signatures, proof bodies, visibility and public imports, is preserved.
The item node's lean.note and proof_origin.note explain withdrawal, and the first proof
step no longer claims the withdrawn module re-exports the source theorem.

## Users

The table lists the full source-only downstream.py closure at the delivery base. Both direct
users are unclaimed. All other users are transitive through the two direct users; their
public interfaces are unchanged because the removed imports are private proof imports.
No target's semantic review is reopened: no definition or mathematical statement changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Adapted: remove one unused proof-only import; all declarations and public imports identical. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Transitive user; unchanged public interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Adapted: remove one unused proof-only import; all declarations and public imports identical. |

## Status

landed 20261017T050317-L-3204663 2026-10-17 (merge of deliver/B3/Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange)
