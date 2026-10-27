# Sheaf.Paper.CondensedTateRealization

## Reason

The new sectionwise encoding proof needs only the existing definitions and the
colimit compatibility API. Narrow two broad public imports (making the
proof-only compatibility import private) and remove eight
redundant imports to avoid loading unrelated proof implementations. No existing
declaration signature or construction changes. The original two
unproved statements and their complete DAG proof routes remain. No target
meaning changes.

Profiling the artifact build also found a 7.28 s instance-attribute application
and 20.3 s of typeclass inference. Local irreducibility of `moduleEncoding`
and restoration of local irreducibility for `integralEncoding` after augmentation
keep these large equivalences behind their existing interfaces. The filled
sectionwise theorem alone locally unfolds both. These attributes are local;
no published definition, declaration type, or reducibility setting changes.
The previous global At additivity attribute is local here; downstream consumers
that need it retain their own local or imported registration.

## Old

```lean
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.Normed.Field.Basic
public import Sheaf.Paper.CondensedERealization
public import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Paper.CompletedRlimFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.AdicCoefficientDatum
```

## New

```lean
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.Normed.Field.Basic
public import Sheaf.Paper.CondensedERealizationDefinitions
public import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Paper.CompletedRlimFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CondensedERealization
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
```

Reviewer correction (cc review, 2026-10-26): the eight plan modules of the two
remaining holes (`integralComparison_existsUnique` cites `completedCondensedIntegral`
of the unit sk-prop-sfb-qlbar-colimit-x; `condensed_tate_realization` cites the
roots-of-unity, local-freeness, tensor, flatness, homotopy-limit, tensor-pullback and
E-realization nodes) are kept as plain `import`s: stage 3 §2 removes a plan import only
once the proof compiles without it, and a unit-route module is not dropped. Only
their public re-export is narrowed; `IntegralUniformCoefficient` and the broad
`TwoColimit` (no proof dependency of the node) stay removed.

Additional local transparency controls in the new file:

```lean
attribute [local irreducible] moduleEncoding
-- after augmentation, before limitAdjunction:
attribute [local irreducible] integralEncoding
-- scoped to encodedBalancedPower_existsUnique:
attribute [local semireducible] integralEncoding moduleEncoding in
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed in shared snapshot | No source adaptation; compiles against the corrected module (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed in shared snapshot | No source adaptation; compiles against the corrected module (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed in shared snapshot | No source adaptation; compiles against the corrected module (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed in shared snapshot | No source adaptation; compiles against the corrected module (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed in shared snapshot | No source adaptation; compiles against the corrected module (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed in shared snapshot | No source adaptation; compiles against the corrected module (reviewer, 2026-10-26). |

## Status

landed 20261026T065049-L-2681765 2026-10-26 (merge of deliver/A4/Sheaf.Paper.CondensedTateRealization)
