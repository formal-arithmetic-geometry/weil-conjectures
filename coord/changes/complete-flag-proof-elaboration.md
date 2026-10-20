# CompleteFlagBundle proof elaboration commands

## Reason

Proving the chart basis, monomorphisms and successive-factor uniqueness requires
BigOperators notation and controlling elaboration of tensor pullbacks, chosen
limits and rank recursion. The static delivery check treats changes to `open`,
options and local attribute commands as an interface change and requests this
record. No public declaration signature or recursive defining equation changes.
`completeFlagBundle` now explicitly requests structural recursion on its rank.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
```

No local reducibility attributes were set in this module.
The recursive definition had no explicit termination annotation.

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject BigOperators
```

The transparency options are enabled only for the recursive proof helpers, after
the geometric declarations. The main transparency option is restored to the
package default before the original last-quotient statement. The chart proof
uses no modified transparency option. The safeguard is enabled again for the
final property statement; the definitions needed only as objects there remain
locally irreducible, avoiding unnecessary instance-search unfolding.

Local irreducibility attributes, only within this module, prevent unfolding of
`Scheme.Modules.tensorPullback`, `completeFlagProjectivization`,
`CategoryTheory.Limits.limit`, `CategoryTheory.Limits.colimit`, `projectiveBundleTensorPullbackIso`,
`Scheme.Modules.tensorPullbackSectionComp`,
`Scheme.Modules.tensorPullbackSectionId`, `completeFlagBundle`,
`completeFlagIdentity`, `completeFlagExtend`, `completeFlagStep`,
`completeFlagQuotient`, `completeFlagPredecessor`, `completeFlagKernel` and
`projectiveBundlePullbackAdjunction`. The original semireducibility of
`completeFlagBundle`, `completeFlagIdentity` and `completeFlagExtend` is restored before subsequent original declarations.
These attributes are local; no exported reducibility attribute is changed.
No notation is declared. Public statements and all original defining equations
remain verbatim. The recursive definition now ends with
`termination_by structural r => r`, retaining its rank-zero, rank-one and
rank-successor equations. Private helpers are proved theorems only.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CompleteFlagBundle --uses
completeFlagBundle` lists the six downstream modules below and reports the
actual declaration use in FlagPullbackInjective and the item itself.
No consumer changes are needed: all public declaration types and definition
bodies remain identical, and the elaboration commands do not export attributes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | E7 | Three theorem proofs completed; local proof elaboration commands added. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No signature or definition change. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No signature or definition change. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No signature or definition change. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No signature or definition change. |
| Sheaf.Paper.LocalizedTopChern | E5 | No signature or definition change. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No signature or definition change. |

## Status

landed 20261020T131953-L-1396445 2026-10-20 (merge of deliver/E7/Sheaf.AlgebraicGeometry.CompleteFlagBundle)
