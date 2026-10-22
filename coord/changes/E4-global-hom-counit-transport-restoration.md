# AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport

## Reason

Restore the quarantined rework item with its original interface. The archive fails
at the rewrite in directImage_naturality because the current adopted
schemeGlobalHomDirectImageMap uses mixedGlobalSectionsDirectImageIso. Use exactly
that comparison's inverse naturality equation. No definition, statement, public
import, instance, or target meaning changes. This is a real compatibility repair
of an archive with zero holes; the delivered module also has zero holes.

## Old

The library path is absent; its preserved source is
quarantine/Sheaf/AlgebraicGeometry/GlobalHomBaseChangeCounitTransport.lean.
The public theorem signature and every helper signature are preserved verbatim.
The two obsolete proof expressions in directImage_naturality are:

```lean
  have hl := (schemeGlobalSectionsDirectImageIso f).inv.naturality
```

```lean
    congrArg ((schemeGlobalSectionsDirectImageIso f).inv.app _ ≫ ·) hn'
```

## New

Restore the full archived module, replacing only those two expressions by:

```lean
  have hl := (mixedGlobalSectionsDirectImageIso f).inv.naturality
```

```lean
    congrArg ((mixedGlobalSectionsDirectImageIso f).inv.app _ ≫ ·) hn'
```

The node's first proof step documents this choice. Its statement, Lean attachment,
and all dependencies remain identical. The quarantine archive is retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | E4 | Restore and repair private proof; identical public interface. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | quarantined | Archived direct importer and caller; its original arguments still match the identical theorem signature. No adaptation required. |

Searching both active library roots finds no current importer or declaration user.
The downstream script reports unknown module, as expected for the absent source.
Searching quarantine finds the consumer listed above. The DAG parent still needs
this result, so it is restored rather than withdrawn. The module compiled without
warnings in 32.8 seconds using lcompile.py. The public signature agrees verbatim
with the archive and existing DAG record. The unit route is preserved and no
consumer changes mathematically.

## Status

landed 20261022T002359-L-1922723 2026-10-22 (merge of deliver/E4/Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport)
