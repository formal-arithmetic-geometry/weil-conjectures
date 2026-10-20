# RationalRetractEvaluation private proof scope

## Reason

The interface scanner records `include` and `omit` commands even when their scope is
one private theorem. These new commands control only the private proof helpers;
no existing public declaration or definition changes its signature or meaning.

## Old

No `omit` or `include` command was present. Both private helpers were absent.
All existing public signatures and definition bodies are unchanged.

## New

```lean
omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem adjoint_evaluation
```

This omits unused geometric assumptions from the private evaluation identity.

```lean
include D hl in
private theorem hom_closed
```

This retains the characteristic datum and its prime-invertibility proof in the
private Hom-closure lemma, whose proposition does not itself mention them.
Each command ends with that private theorem. Neither changes exported instances,
notation, attributes, public declarations, or later section-variable scope.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Private proof helpers only; public API unchanged. |

There are no external users of these private helper commands. All importing
modules see exactly the original public statements and definitions.

## Status

landed 20261020T051005-L-1520720 2026-10-20 (merge of deliver/A4/Sheaf.SixFunctors.RationalRetractEvaluation)
