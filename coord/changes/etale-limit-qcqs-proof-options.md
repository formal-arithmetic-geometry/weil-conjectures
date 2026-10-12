# etale_limit_cohomology_qcqs_gluing

## Reason

The delivery's proof uses a fully quantified affine-continuity hypothesis with named
proof binders unused inside its result type. A declaration-scoped unused-variable
linter setting suppresses those warnings while preserving the signature verbatim.
A transparency setting prevents needless unfolding in elaboration of the cover
induction. The static checker treats these commands as an interface change, although
neither changes any declaration's type or mathematical meaning.

## Old

The original module contains no explicit transparency or unused-variable linter setting.
The theorem signature is unchanged, including every binder, universe and name.

## New

```
set_option backward.isDefEq.respectTransparency true
```

and directly before the original theorem's docstring:

```
set_option linter.unusedVariables false in
```

The first affects only elaboration of this file and the second only its declaration's
linting. These options export no definition, notation, instance, axiom or signature.
The new stage-continuity predicate and smaller lemmas are additions in their own new
modules, imported only for the original theorem's proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing | E3 | Proof elaboration and linting only; unchanged theorem type. |

No existing public declaration or definition changed. Consequently no downstream
module requires adaptation, and no target's statement or definitions change.

## Status

landed 20261012T112835-L-766268 2026-10-12 (merge of deliver/E3/Sheaf.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing)
