# Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence imports

## Reason

The public ModuleCat.Abelian import is redundant: the existence theorem mentions no
ModuleCat, and compiles without that import. Removing it keeps imports minimal.
No declaration, definition, or theorem signature changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Abelian
```

## New

```lean
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
```

## Users

`tools/downstream.py` reports 1371 transitive consumers. A direct-import source search
finds exactly one direct consumer, below. It imports this module privately, so this
module's public imports are not re-exported through that edge. It also already publicly
imports ModuleCat.Abelian independently. Consequently neither its interface nor any
transitive consumer's interface loses that import. No forced adaptation is required.
The original direct consumer and its original compatibility dependency were compiled
in scratch copies with the modified existence module, using lcompile.py --all; all
three compiled successfully. Scratch consumers were removed from the delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge | unclaimed in local claims snapshot | no effect: independent public ModuleCat.Abelian import retained; original compiles |

No definition used by a target changed, so no target-statement review is reopened.

## Status

landed 20261014T001717-L-2549231 2026-10-14 (merge of deliver/F3/Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence)
