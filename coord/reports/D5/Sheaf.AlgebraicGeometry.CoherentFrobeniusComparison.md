## What changed

Restored the quarantined module
`Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison` and retained its existing
proof of `AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison`. The proof
assembles the three declared comparison lemmas: coherent power semilinearity and
naturality, the coherent-etale pullback square, and coherent Frobenius pullback
naturality. No statement or target declaration changed.

The delivery also changes the item import of `CoherentFrobeniusPullback` from private to public and removes the now-redundant direct public import of `CanonicalCoherentEtaleComparison`; this is the item interface change required by the forced-adaptation protocol. It adapts the held dependency
`Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` by removing one private import
that triggers a duplicate declaration in the current published build. Its theorem
signature and body remain unchanged.

## Proved and sorry left

Closed the item hole:
`AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison`
(node `lem-weil-pbc-coherent-frobenius-comparison`). The item has zero sorries.

The adapted dependency retains its pre-existing named hole:
`AlgebraicGeometry.Scheme.Modules.coherentFrobenius_pullback`
(node `new-coherent-frobenius-pullback`). This delivery does not add a new theorem
or a new sorry; the item proof uses this declared dependency exactly as planned.
The imported `coherentPowerComparison` and
`coherentEtaleComparison_pullback` holes remain in their existing modules and nodes.

## No longer needed

The item proof does not need the former direct Cech, affine-vanishing, flat
separatedness, or explicit base-change-construction imports. It uses only the three
comparison modules, the canonical comparison API, module cohomology map, tensor
structure-sheaf API, and the standard categorical imports already present in the
restored item. No DAG node is newly pruned by this restoration; the existing item
proof dependencies agree with the proof. The public dependency import is retained so the adapted dependency is part of the item interface; the direct canonical-comparison import is redundant through that dependency.

## Forced adaptations

The item interface and adaptation records are `coord/changes/D5-coherent-frobenius-interface.md` and
`coord/changes/D5-coherent-frobenius-pullback-import.md`.

The forced adapted module is `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback`, held by A2.

The original dependency failed while compiling against the current published build:

```text
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality failed,
environment already contains
'AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv'
from Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

This error is reached through the dependency's private import of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge`. Removing that
single import is necessary for the item to compile. The dependency's theorem
signature, visibility, and all declarations are unchanged. The adapted module is
held by A2; no other lines are changed.

## Where the brief, the DAG or earlier work was wrong

The prior delivery was quarantined after an upstream sync because the dependency
object was unavailable. The item proof itself was already complete and matches the
existing DAG proof steps. The current published build also exposes a stale duplicate
between the Sheaf and upstream Ext-resolution modules; the forced private-import
adaptation records that build-state issue without changing the mathematical route.

## New nodes

None.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback
Only imports removed (WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
