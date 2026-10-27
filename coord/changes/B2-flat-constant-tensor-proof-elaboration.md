# CategoryTheory.flatConstantTensorProZeroCones

## Reason

The completed proof needs private helpers for exact scalar extension, natural cone
transport, the normalized coefficient unit, and derived-limit comparisons. Specializing
these helpers unfolded large sheafification and total-tensor constructions. Local
reducibility attributes keep those constructions folded while applying their proved APIs.
The complete module then compiles cleanly through lcompile.py in 50.1 seconds.

The stage-3 interface scanner records changes to commands conservatively, including local
attributes, namespace commands and scoped options. This record documents that finding.
Every existing public signature, definition body, instance body, visibility and public
import stays verbatim. There is no change of the mathematical object or of a target's
meaning. No other module is adapted, and no source-library module is changed.

## Old

There were no additional local irreducibility attributes and no private unit-proof
namespace. The existing local instance commands, retained verbatim, include:

```lean
attribute [-instance] flatConstantExtensionAdditive
attribute [local instance] flatConstantExtensionAdditive
```

The original main theorem had its current signature and the proof `:= sorry`.
All existing declarations keep exactly their original signatures and all existing
non-theorem bodies keep exactly their original text.

## New

The main theorem has a complete proof. The added local reducibility commands are:

```lean
attribute [local irreducible] levelConeTower FlatConstantConeProZero
  flatConstantPointedLimitMap flatConstantStrictConeMap

attribute [local irreducible] flatConstantExtensionModel

attribute [local irreducible] flatConstantTensorFunctor
  FlatConstantUnitProof.coefficientIso flatConstantTensorUnit FlatConstantUnitNormalized
```

`levelConeTower` and `FlatConstantUnitProof.coefficientIso` are new proved private
constructions. The other names above are existing public declarations; their signatures
and bodies are unchanged. The attributes are local to this module's namespace scope and
do not alter the attributes visible to an importing module.

`namespace FlatConstantUnitProof` contains only private definitions and proved private
lemmas. Its options are scoped to that namespace:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Some private helpers also use a declaration-scoped
`set_option backward.isDefEq.respectTransparency false in` or `omit ... in` to select
exactly their actual hypotheses. No scoped option or private declaration is inserted
into a public definition's body. The original public instances retain their original
instance attributes; no new exported instance is introduced.

## Users

Read-only consumer check:

```text
python3 tools/downstream.py Sheaf.CategoryTheory.FlatConstantTensorProZeroCones --uses
  FlatConstantConeProZero flatConstantPointedLimitMap flatConstantStrictConeMap
  flatConstantExtensionModel flatConstantTensorFunctor flatConstantTensorUnit
  FlatConstantUnitNormalized
```

The check reports zero downstream modules. Each queried name is mentioned only in the
item module. Planned DAG consumers remain attached; none is withdrawn or weakened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FlatConstantTensorProZeroCones | B2 | Sole hole proved; local proof elaboration commands added; all existing public signatures and non-theorem bodies preserved. |

There are no downstream Lean consumers to adapt. The existing DAG node has only its proof,
proof dependencies and proof origin updated to match the implementation. Its statement,
statement dependencies and Lean attachment are unchanged. The proper-base-change unit
route and all target statements and definitions are unchanged.

## Status

landed 20261022T142413-L-731180 2026-10-22 (merge of deliver/B2/Sheaf.CategoryTheory.FlatConstantTensorProZeroCones)
