# Sheaf.AlgebraicGeometry.EtaleReplacementStageDiagram imports

## Reason

`Mathlib.CategoryTheory.Abelian.FunctorCategory` supplies the abelian instance used
in the objectwise short-exactness proof. The existing theorem signature only needs
zero morphisms in the functor category and the definition of ShortExact, already
available through the unchanged public imports. This is a proof-only dependency
and must be an ordinary import under coord/brief-stage3.md §2.
No declaration signature, definition, instance declaration or target meaning changes.

## Old

```lean
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
```

## New

```lean
import Mathlib.CategoryTheory.Abelian.FunctorCategory
```

## Users

The source-only downstream search reports one direct importer and 268 transitive
importers; `--uses etale_replacement_stage_diagram` reports the item itself and the
one direct importer below. That direct importer imports this module ordinarily,
so the removed public import was never reexported by it to the transitive users.
A scratch copy of its unchanged source compiled against the delivered modules
with lcompile.py in 16.5 seconds. No adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleReplacementStageDiagram | F1 | The proof retains its dependency; signature unchanged, compilation clean. |
| Sheaf.AlgebraicGeometry.EtaleLimitReplacementExactSystems | unclaimed | Unchanged source compiles against the delivered overlay; statements and proofs unchanged. |

## Status

landed 20261012T184254-L-4001569 2026-10-12 (merge of deliver/F1/Sheaf.AlgebraicGeometry.EtaleReplacementStageDiagram)
