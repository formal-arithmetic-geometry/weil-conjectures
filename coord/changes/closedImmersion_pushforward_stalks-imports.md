# closedImmersion_pushforward_stalks imports

## Reason
The proof uses Mathlib scheme modules and germs directly. The custom tensor pullback,
custom presheaf-module stalk functor, and scheme closed-immersion API are unnecessary.
Use the public imports needed by the unchanged theorem signature and a plain import
for the zero-group fact used only in its proof. No definition or theorem signature changes.

## Old
```lean
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Topology.PresheafModuleStalkFunctor
```

## New
```lean
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.Grp.Zero
```

## Users
The eight direct importers were inspected. They import this result only for proofs,
and obtain their tensor pullback and closed-immersion APIs through other imports.
Their statements and definitions therefore retain their meanings. No adaptations needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteSurjectiveCoherentGenericSupport | none adapted | Explicit imports of TensorPullback and ClosedImmersion retained. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | none adapted | Explicit imports of TensorPullback and ClosedImmersion retained. |
| Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence | none adapted | Imports Annihilated, FullyFaithful, and IdealPowers, which retain these APIs. |
| Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated | none adapted | Explicit imports of TensorPullback and ClosedImmersion retained. |
| Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion | none adapted | TensorPullback retained; closed-immersion API also available through the other imported closed-immersion modules. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes | none adapted | TensorPullback retained; closed-immersion API also available through the other imported closed-immersion modules. |
| Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful | none adapted | Explicit public imports of TensorPullback and ClosedImmersion retained. |
| Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient | none adapted | Explicit imports of TensorPullback and ClosedImmersion retained. |

## Status
landed 20261012T063509-L-3154794 2026-10-12 (merge of deliver/G1/Sheaf.AlgebraicGeometry.ClosedPushforwardStalks)
