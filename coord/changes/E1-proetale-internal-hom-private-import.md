# AlgebraicGeometry.ProEtale.CondensedRing.supportPullback_ihomComparison_isIso

## Reason

Restore the quarantined module after the upstream-verbatim sync. Its proof uses the
private tensor presentation comparison `Mod.relativeTensorRightIso`, together with
`Mod.relativeTensorπ` and `Mod.relativeTensorCofork`. The sync moved these helpers
from the upstream module into the existing Sheaf.UpstreamExtra module. The old
`import all` therefore opens the wrong module's private declarations. Import all
from their actual home instead. Also omit an unused MonoidalPreadditive hypothesis
from the private embedding lemma to keep compilation warning-free.

## Old

The quarantined source contains:

```lean
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

and its private `concreteIhomIso_embedding` unnecessarily includes
`[MonoidalPreadditive C]` from the surrounding section.

## New

```lean
import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

Place `omit [MonoidalPreadditive C] in` before the private embedding lemma.
All archived public signatures, attributes, definitions, and public imports are
preserved. The public internal-Hom comparison remains the canonical evaluation
comparison for the same supportPullback functor and relative monoidal structure.
There is no change to any target meaning and no new construction or proof hole.
The existing DAG attachment and all its dependencies remain valid unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtalePullbackInternalHom | E1 | Restore the archived module with the repaired private import and private lemma. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteProjectiveDualizable | unclaimed in local snapshot | Quarantined direct importer; its use of supportPullback_ihomComparison_isIso retains exactly the same type; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | unclaimed in local snapshot | Quarantined indirect consumer through ProEtaleFiniteProjectiveDualizable; no interface change or adaptation. |

No live Lean source imports the missing module. Quarantined sources were searched
as well; their modules are preserved, not withdrawn. No source-library file is edited.

## Status

landed 20261020T145501-L-2400506 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.ProEtalePullbackInternalHom)
