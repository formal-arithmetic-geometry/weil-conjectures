## What changed

Repaired the returned delivery by replacing the absent resolution-map changes with
one proof-only import of the library's existing
`Sheaf.Paper.ModuleCupCoefficientResolutionMaps`. Proved
`AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality` from its
simultaneous computing resolutions. Private, proved helpers establish surjectivity
of resolution class maps and construct the paired cocycle from Leibniz. The proof
transports three cycles by cochain maps and combines their class equations with
both cup-product characterizations. All public signatures and visibility remain
unchanged. The existing node now records this argument and its dependency.

## Proved and sorry left

Closed one of the two existing holes:
`AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
The sole remaining hole in the delivered module is
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`
(blueprint: `lem-sc-picard-cech-cup-pullback-compat`), unchanged with its source
and proof in words. No holes were added or split off. The five previously proved
public declarations remain proved. The coefficient proof uses the existing
`moduleCup_coefficient_resolution_maps`; its underlying Godement construction
remains a dependency of the library, not a new hole in this delivery.

## No longer needed

No imports or existing proof-dependency nodes were removed. The returned proposed
changes to `Sheaf.Paper.ModuleCupCoefficientResolutionMaps` and the proposed
`Sheaf.Paper.ModuleCupPullbackResolutionMaps` are not needed in this partial
repair: the first interface already exists unchanged in the library, and the
second is not imported or delivered. No new modules are added.

## Where the brief, the DAG or earlier work was wrong

The returned environment collision between `ModuleCupKInjectiveTarget` and
`GlobalTensorPullbackMonoidalNormalization` does not recur against the current
published build: the assigned module with its required `CechCupProduct` import
compiled cleanly before editing. No alteration of those dependency modules is
necessary or included. The actual repair closes the coefficient naturality hole
using the now-existing resolution-map API, rather than repeating the old delivery.

The three returned importer failures are addressed by retaining every existing
public signature and visibility in `CechCupPullbackCompat`, making only a
proof-private import, and delivering no replacement interface for either named
resolution-map module. Thus the incompatible resolution-map changes causing those
failures have been dropped. Compilation and the delivery probe validate the
combined imported environment, including the required cup-product import.

## Second reading by X2

1. **Diff and interfaces.** Compared the delivered module with the repository version. The only interface-visible change is the proof-only import of `Sheaf.Paper.ModuleCupCoefficientResolutionMaps`; all existing declaration signatures and visibility are unchanged. Verdict: pass.

2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it compiled cleanly. The module contains only the documented remaining `moduleCup_pullback_naturality` sorry, with no forbidden declarations or hollow definitions. Verdict: pass.

3. **Split statements.** No statements or modules were split off in this delivery. The remaining hole is the original named theorem and its existing node; no duplicate intermediate statement was introduced. Verdict: pass.

4. **Route and pruning.** The coefficient proof follows the existing simultaneous-resolution route, using the published resolution-map interface; the Cech comparison and cup-product route remains intact. The added import is needed by the proof and no old proof dependency became unused. Verdict: pass.

5. **DAG agreement.** The node records the repaired coefficient proof and its resolution-map dependency, while retaining the unchanged pullback hole and unit route. Verdict: pass.

Changed during this second reading: no Lean declarations or DAG statements; added this review section only.
