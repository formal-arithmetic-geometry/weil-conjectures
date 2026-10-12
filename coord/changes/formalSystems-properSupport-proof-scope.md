# AlgebraicGeometry.formalSystems_properSupport_serre: proof scope commands

## Reason

The delivery adds a noncomputable section for private proof helpers, opens the scoped
zero-object notation, and sets elaboration and linter options locally for the unchanged
public theorem. The static interface checker flags changes to these commands and requests
this record. No definition, theorem signature, visibility, instance or public import
changes. This is an account of proof scope, not a mathematical statement correction.

## Old

The existing module header and scope, verbatim:

```lean
@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
```

The existing theorem has no command-local options before its docstring.

## New

The same header/scope with proof notation and private helper scope:

```lean
@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry

noncomputable section
```

The helper section is closed before closing the namespace. The original public theorem
signature is byte-for-byte unchanged. Immediately before its existing docstring:

```lean
-- The original quantified instance binder is used implicitly in the statement.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The scoped opening enables `0` for categorical zero objects. The noncomputable section
permits standard categorical constructions inside the proofs. Both are confined to this
file. The command-local options apply to this theorem only; none changes importer
elaboration. The local unused-variable option handles the original named quantified
instance binder. The theorem is compiled with its existing type and public visibility.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre
--uses formalSystems_properSupport_serre` reports one actual consumer besides the module
itself, out of 191 downstream modules. The direct importer is the same consumer.
There are no adaptations; scoped openings and command-local options do not propagate
through module imports. Every downstream statement and definition keeps its meaning.
No target statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre | C1 | Proofs and local scope only; unchanged signature. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | Same theorem interface and meaning; no adaptation required. |

## Status

landed 20261012T184244-L-3996869 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre)
