# Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport proof commands

## Reason

The preflight scanner requests a change record for the commands accompanying the
four completed proofs. The added elaboration option permits the proof calculations
through the existing derived comparison definitions. The `omit ... in` commands
restrict unused ambient instances of proved private helpers. Two theorem-local
linter settings preserve the existing public signatures despite unused hypotheses.
No public signature, definition, import, notation or instance changes. The initial
packet's private instance was removed: its use is now an explicit instance binder
on the private inverse lemma, supplied by local hypotheses in its consumer.

## Old

No added option, omission or helper commands. The four theorem proofs were `by sorry`.
All existing public declaration signatures are retained verbatim.

## New

```lean
set_option backward.isDefEq.respectTransparency false
```

Private proved helpers have declaration-scoped `omit ... in` commands. The existing
independence theorem has `set_option linter.unusedSectionVars false in`; the existing
coherence theorem has `set_option linter.unusedVariables false in`. These options
control elaboration and linting within this file. There are no added instances,
attributes, notation, imports, public declarations or changes to existing bodies
other than the four theorem proofs.

## Users

`tools/downstream.py` reports zero downstream modules and only this module as a
textual user of the four theorem names. The DAG attachment and parent route remain.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport | Z8 | Four proofs filled; private helpers and file-local proof elaboration commands added. |

## Status

landed 20261021T165949-L-2317612 2026-10-21 (merge of deliver/Z8/Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport)
