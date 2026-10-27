# AlgebraicGeometry.Scheme.Modules.canonical_proj_open_cover_gluing

## Reason

The proof now uses two strictly smaller section-algebra/canonical-map descent statements
and proves the final open-immersion step. Remove redundant direct imports, including the
public import of the algebraic-space canonical-map theorem: it is a proof dependency of
the new evaluation-descent statement, not a declaration needed by this module's signatures.
Every existing declaration signature, definition body, attribute and visibility is unchanged.
This record documents only the changed public import closure.

## Old

```lean
public import Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.TraceFormula.SpaceLineModuleProjMap
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Sheaf.AlgebraicGeometry.CoherentFiniteType
```

## New

```lean
public import Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Sheaf.AlgebraicGeometry.SectionAlgebraOpenCoverDescent
import Sheaf.AlgebraicGeometry.SectionAlgebraCanonicalMapOpenDescent
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalProjOpenCoverGluing | A6 | Proof and imports changed; identical three public declarations. |

`tools/downstream.py Sheaf.AlgebraicGeometry.CanonicalProjOpenCoverGluing --uses
canonical_proj_open_cover_gluing` reports zero downstream modules; the only declaration
name occurrence is in this module itself. A direct-import search across both library roots
also finds no importers. Thus no consumer adaptation or consumer compile is necessary.
The unfinished DAG parents and all unit dependencies are preserved; the item is not withdrawn.
No target statement or definition meaning changes.

## Status

landed 20261026T080823-L-1608203 2026-10-26 (merge of deliver/A6/Sheaf.AlgebraicGeometry.CanonicalProjOpenCoverGluing)
