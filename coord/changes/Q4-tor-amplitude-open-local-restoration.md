# AlgebraicGeometry.torAmplitude_of_open_neighbourhoods

## Reason

Restore the assigned quarantined module. Its archived implementation imports the retired
Sheaf derived pullback; the recorded failure is a duplicate derivedPullback declaration.
Changing only that import reveals the next duplicate, schemeDerivedTensorCohomologyVanishes.
The adopted source module already contains the byte-identical public theorem statement
and complete proof, with current IsKFlatTensor and derivedPullback_spec APIs.
Reuse that proof through a compatibility import. The archive remains untouched.

The retirement census classified this pair as DIFFERENT because its private K-flat helpers
use the current IsKFlatTensor name. Both public import and proof-only import all are retained:
the latter preserves private-helper access for consumers using import all on the Sheaf path.
This was checked using a separate consumer compiled against the sandbox artifact.
No source-library file is changed, and no theorem, definition or target meaning changes.

## Old

The assigned source is quarantine/Sheaf/AlgebraicGeometry/TorAmplitudeOpenLocal.lean.
Its direct imports were:

```lean
public import WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.AlgebraicGeometry.SheafZeroStalks
```

Its public signature, byte-identical to the upstream signature and DAG lean.statement, is:

```lean
theorem torAmplitude_of_open_neighbourhoods (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (a b : ℤ) (hab : a ≤ b)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
        i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes U.toScheme
          ((derivedPullback U.ι).obj E) G i) :
    ∀ (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
      i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
```

The restored module re-exports the existing theorem, rather than declaring it twice.
Its DAG lean.module and lean.file point at the actual upstream declaration; lean.note
records the restoration. All mathematical statement and proof dependencies stay intact.
The upstream proof still constructs K-flat models, identifies derived open restriction,
transports tensor homology and applies isZero_of_iSup_eq_top.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal | Q4 | Restore compatibility path, keeping public theorem and import-all helper access. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | unclaimed; quarantined | Its import all uses open_pullback_restriction_iso; the identical helper signature remains available. No forced adaptation. |
| WeilConjectures | unclaimed | Imports canonical source directly; unchanged. |
| WeilConjectures.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude | unclaimed | Already imports all canonical source and uses its current private helpers; unchanged. |
| WeilConjectures.AlgebraicGeometry.AffineQCohTorAmplitudeDetection | unclaimed | Already imports all canonical source; unchanged. |
| WeilConjectures.AlgebraicGeometry.DerivedTensorVanishingRetract | unclaimed | Already imports all canonical source; unchanged. |
| WeilConjectures.AlgebraicGeometry.QuasiCompactFiniteTorDimension | unclaimed | Uses the byte-identical public theorem from the canonical source; unchanged. |
| WeilConjectures.AlgebraicGeometry.TorAmplitudeQCohTest | unclaimed | Already imports all canonical source; unchanged. |

Source searches and tools/downstream.py --direct find no current Lean importer of the
missing Sheaf path, and six direct canonical importers, listed above. The archived
PerfectDegreeZeroFibreCriterion consumer was read as well; its other quarantine issues
are independent. No consumer file or file held by another group is changed.
No DAG node is deleted, and no parent dependency is withdrawn.

## Status

landed 20261020T211817-L-3504910 2026-10-20 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal)
