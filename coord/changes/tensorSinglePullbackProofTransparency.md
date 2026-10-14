# tensorSinglePullback_composition proof transparency

## Reason

The new proved private helpers require the tensor-pullback functor to stay folded
while categorical naturality and composition equations are elaborated. After the
naturality helper, the canonical single-pullback map likewise stays folded for the
generic composition calculation. Both attributes are local to this module; they
change no exported declaration, instance, signature or definition body. The
proof-local `cleanup.letToHave false` option preserves the named functor
bindings used in the repaired naturality calculation. Two elementary private
category calculations combine the component equalities without repeatedly
normalizing the concrete derived functors. The static checker classifies added
attribute and option commands as interface-sensitive; none changes the exported API.

## Old

No local transparency attributes on these declarations in the assigned module.

## New

```lean
set_option cleanup.letToHave false
attribute [local irreducible] Scheme.Modules.tensorPullback
attribute [local irreducible] canonicalSinglePullbackMap
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition | K3 | Proof elaboration only; every existing signature is identical. |
| Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting | unclaimed | None: the attributes are local and neither exported nor inherited. No adaptation. |

## Status

landed 20261014T033106-L-603824 2026-10-14 (merge of deliver/K3/Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition)
