# CategoryTheory.exists_coveringRepresentable_coequalizer (imports)

## Reason

Second reading found an unnecessarily broad public import of sheaf cohomology, used only
for the type-valued sheafification instance. Replace it with its actual provider,
`Mathlib.CategoryTheory.Sites.LeftExact`, which the unchanged statement needs to elaborate
`presheafToSheaf`. Remove redundant direct imports: `LeftExact` publicly imports `Sites.Limits`
and `Sites.Sheafification`; `PrecoverageToGrothendieck` publicly imports `Hypercover.Zero`,
which publicly imports `Limits.Shapes.Products`; these paths also provide `Limits.HasLimits`.
The two proof-only imports remain plain imports. No declaration signature, visibility,
definition, or target meaning changes; no target statement review is reopened.

## Old

```lean
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
```

## New

```lean
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
```

## Users

Snapshot from `tools/downstream.py` of all 19 downstream modules; group labels reflect
recorded claims at the second reading. The only direct importer is
`Sheaf.CategoryTheory.Sites.LowerShriekCoveringGenerators`. It imports this module privately
and independently imports `SheafCohomology.Basic` publicly, so the reexport change cannot
remove any declaration available to its own users. Its unchanged source compiles against
the revised compiled module. There are no forced adaptations and no semantic effects.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | E1 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | D2 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.CategoryTheory.Sites.LowerShriekCoveringGenerators | F2 | Unchanged source compiled against the revised module; retains its own public `SheafCohomology.Basic` import. The presentation remains a proof dependency. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| TargetsCheck | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | No signature or definition changes. Reexports of its direct dependency are unchanged; no adaptation. |

## Status

landed 20261015T182201-L-784702 2026-10-15 (merge of deliver/C3/Sheaf.CategoryTheory.Sites.CoveringRepresentableCoequalizer)
