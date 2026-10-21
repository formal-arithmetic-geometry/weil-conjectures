# WeilConjectures.PurityFiniteSetting.finiteClopen_scalar_extension

## Reason

Eight existing proofs are filled without changing any public signature, public import, or
non-theorem body. The command-change preflight check requests this record for local elaboration
settings. Repeated unfolding of the completed scalar and pullback functors made elaboration too
slow. Local irreducibility keeps these functors folded while the proved private comparison
helpers assemble the scalar square. The complete module compiles in 44.1 seconds.

The unused-section-variable linter is disabled in this file to preserve the published theorem
parameters while proving clauses that do not use every parameter. This is a diagnostic setting,
not a change to implicit parameter inclusion or to any theorem statement.

## Old

There was no local irreducibility command for these four definitions and no
`linter.unusedSectionVars` setting. The adjacent existing settings were:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Every existing declaration signature and every non-theorem body is preserved verbatim, modulo
whitespace. No existing definition is replaced or modified.

## New

```lean
set_option linter.unusedSectionVars false
```

and, within the existing noncomputable section:

```lean
attribute [local irreducible] integralDerivedPullback integralScalarExtension
  scalarCompletion integralOrdinaryScalar
```

These attributes are local to this section. They are not exported to importing modules.
The private helpers are proved and do not appear in any public signature or definition body.
The theorem proofs may reference private proved helpers, as permitted by the module interface.
All 41 existing public declaration signatures and all public imports remain unchanged.
No target meaning changes, no statement repair, and no forced adaptation are involved.

## Users

Checked with:

```
python3 tools/downstream.py Sheaf.Paper.FiniteClopenDerivedDecomposition --uses integralDerivedPullback integralScalarExtension scalarCompletion integralOrdinaryScalar
```

The script reports zero downstream modules and uses only in the item module. A separate exact
import search under both library roots also finds zero current direct importers. This is a
consumer check, not a claim that the node is unnecessary: unfinished parent proof plans retain
its statement and dependencies. No consumer was changed or separately compiled.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | D9 | Local elaboration keeps scalar functors folded; existing public signatures, definitions, and public imports stay unchanged. |

## Status

landed 20261021T100920-L-4171059 2026-10-21 (merge of deliver/D9/Sheaf.Paper.FiniteClopenDerivedDecomposition)
