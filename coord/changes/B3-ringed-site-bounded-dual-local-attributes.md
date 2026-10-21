# CategoryTheory.RingedSiteBoundedDual: local proof attributes

## Reason

The proof uses the product-limit and component-differential API rather than unfolding the
chosen Hom-complex construction. Local irreducibility keeps elaboration on that API.
Preflight classifies the added attribute command as an interface-level command and requires
this record. The command is local to this module's section: it changes no declaration,
exported attribute, statement, definition body, or public import.

## Old

There was no local reducibility override in the assigned module. All existing public
declaration signatures and definition bodies are retained verbatim.

## New

```lean
attribute [local irreducible] homComplexFunctor homComplexπ
```

This command occurs after `component` and before the proved private helpers. The attributes
expire at the end of the section; importing modules receive the original reducibility.
The three added imports are private proof imports. Twelve new private helper declarations
support the proof; none occurs in an existing public signature or definition body.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents | B3 | Local proof elaboration only; the original theorem is proved unchanged. |

`tools/downstream.py Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents --uses
CategoryTheory.RingedSiteBoundedDual.component` reports zero downstream modules and only
the assigned module as a textual user of `component`. A direct import search likewise
finds no current Lean importer. DAG parents remain attached and need no adaptation:
all existing public signatures, bodies of definitions, visibility and public imports are
unchanged. No target's mathematical interpretation changes.

## Status

landed 20261021T172354-L-3358153 2026-10-21 (merge of deliver/B3/Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents)
