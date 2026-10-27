# AlgebraicGeometry.Scheme.finite_etale_trace_image

## Reason

Restore the module assigned to F2 by the 2026-10-24 rework row. The library path
is absent; its complete proof is preserved in the quarantine archive. The sync
log reports an unknown finiteEtaleTrace_section_sum_descent. The current archive
already imports its correct owner, Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent,
and compiles against the published build. Restore that pro-etale proof, rather
than substituting the distinct etale-site theorem in the source library.

## Old

lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceImage.lean is absent.
The complete source is preserved at
quarantine/Sheaf/AlgebraicGeometry/FiniteEtaleTraceImage.lean.
Its relevant import block is:

```lean
public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSheetLifting
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.ULift
```

## New

Restore the archived file at its library path, preserving every declaration,
signature, definition body and theorem proof. Remove two redundant private
imports; the remaining block is:

```lean
public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSheetLifting
import Mathlib.CategoryTheory.Sites.Subsheaf
```

Preserve the quarantine archive and the existing DAG attachment and dependencies.
The restored trace chooses only the uniquely characterized descended sum.
No target statement or definition changes meaning.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage | F2 | Restored at its original path; complete archived proof and public API preserved. |
| Sheaf.Paper.ContinuousFiniteEtaleTraceLattice | unclaimed | DAG parent and proof-docstring reference; no code adaptation required. |

The downstream.py query reports an unknown module because the library file is
quarantined. Direct searches of lean/Sheaf, lean/WeilConjectures and
quarantine/Sheaf find no executable reference or importer outside the archive.
The DAG parent lem-sfb-continuous-finite-etale-trace-lattice and the unit's trace
step still need this node; absence of current Lean importers does not justify
withdrawal. No consumer is edited.

## Status

landed 20261024T185143-L-3445502 2026-10-24 (merge of deliver/F2/Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage)
