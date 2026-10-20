## What changed

Reworked `lean/Sheaf/AlgebraicGeometry/TorAmplitudeOpenLocal.lean` in the assigned
rework sandbox. The compatibility module continues to publicly import the canonical
`WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal` declaration and to use its
proof-only `import all` interface. I clarified the module documentation to state that
the Sheaf path is restored after the upstream synchronization removed duplicate Sheaf
implementations. No declaration, import, signature, or theorem body was changed.

The module compiles with `lcompile.py` in 2.8 seconds. The existing canonical theorem
has the exact DAG statement and is complete; its axiom set is the permitted standard
set (`propext`, `Classical.choice`, and `Quot.sound`).

## Proved and sorry left

This is a rework repair with zero direct holes before and after. There are no `sorry`s
in the item and no new declarations. The existing theorem
`AlgebraicGeometry.torAmplitude_of_open_neighbourhoods` remains supplied by the
canonical upstream module and is unchanged.

## No longer needed

The archived duplicate implementation and its direct imports remain unnecessary for
the restored compatibility path: the canonical upstream module supplies the theorem,
K-flat model, derived tensor comparison, open restriction, and cover argument. No DAG
node or source module is withdrawn, because the archived implementation is preserved
for the rework record and the canonical module is still used by its consumers.

Searches were run with `msearch.py` (LeanFinder: no Tor-amplitude match; Loogle: no
matching declaration; grep: no additional local declaration). No extra proof imports
are needed.

## Where the brief, the DAG or earlier work was wrong

The rework row describes an import conflict caused by duplicate declarations after the
upstream synchronization. Replacing only the retired derived-pullback import would
still expose the next duplicate tensor-vanishing declaration. The prior restoration
correctly re-exports the canonical upstream module; this packet preserves that repair
and updates only its explanatory documentation.

## New nodes

None.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
