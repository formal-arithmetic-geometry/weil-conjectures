# WeilConjectures.IntegralCoefficientPresentation proof scope

## Reason

The proof adds `open CategoryTheory.Functor` inside this file's existing namespace.
It makes the derived-functor composition API available to the new private helpers.
The preflight classifies this command as a change outside theorem bodies and requests
this record. The command affects name resolution in this file; it introduces no public
notation or instance. Every existing public declaration signature and definition body
is unchanged. The original `comparison` statement is proved verbatim.

## Old

The existing general namespace opening was:

```lean
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
```

There was no `open CategoryTheory.Functor` command.

## New

The existing general opening is retained verbatim. Before the private derived coherence
helpers, the following command is added:

```lean
open CategoryTheory.Functor
```

The proof imports are private imports. The original public imports, universe declarations,
options, attribute command, variables, definitions and theorem statement are retained.
All added declarations are private and fully proved. No target meaning changes and no
statement review is reopened by this proof-scope command.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCoefficientPresentationComparison | G3 | Proof name resolution only; complete proof and private helpers added. |

A search of `lean/Sheaf`, `lean/WeilConjectures` and `quarantine` found no current Lean
importer of this module or qualified consumer of its declarations. Its DAG parents and
unit route remain attached and unchanged; no parent or other module is adapted.
The quarantined parent IntegralStratifiedPerfectCharacterization is preserved.

## Status

landed 20261021T143906-L-17757 2026-10-21 (merge of deliver/G3/Sheaf.Paper.IntegralCoefficientPresentationComparison)
