# Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization

## Reason

The stage-3 preflight conservatively classifies added command scopes as an interface
change. This record documents those scopes. All nine existing public declaration
signatures, both public definition bodies, public imports, and declaration attributes
are unchanged. No mathematical statement or target interpretation changes.

The seven existing theorem holes are proved. New helpers are private, proved theorems.
Scoped `omit` commands keep irrelevant derived-category instances out of the purely
complex-level private helpers. Scoped elaborator options permit the canonical complex
and localization identifications in the proofs. They end at their associated declaration.
Two scoped linter settings preserve inherited hypotheses without warnings.

## Old

The inherited variable command is preserved verbatim:

```lean
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
```

There were no additional local elaboration, omission, or linter scopes. The seven
theorem bodies were `by sorry`.

## New

The inherited variable command above remains identical. Individual private helpers or
existing theorem proofs use the following declaration-scoped options, where needed:

```lean
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
```

The complex-level private helpers use one of these declaration-scoped commands:

```lean
omit [HasDerivedCategory C] in
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
```

The inherited `goodTruncationProjection_condition` retains its original implicit
instances, with `set_option linter.unusedSectionVars false in` scoped to that theorem.
The inherited `goodTruncationNormalization_exact` retains the original binder `hL`,
with `set_option linter.unusedVariables false in` scoped to that theorem: its second
conjunct is naturality on arbitrary objects, so the concentration of L is unnecessary
to its proof. No scope adds an instance, attribute, notation, or public declaration.

The seven theorem proof bodies are complete. The public definitions
`DerivedCategory.goodTruncationProjection` and
`DerivedCategory.goodTruncationNormalization` remain verbatim.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization`
reports zero downstream modules. A direct import and declaration-use search of
`lean/Sheaf` and `lean/WeilConjectures` likewise finds only the item itself.
Pending DAG parents retain the same statements and attachments; the item is preserved.
No consumer needs adaptation, and no target-definition review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization | Z9 | Private proof helpers and declaration-scoped options; all existing public interfaces unchanged. |

## Status

landed 20261021T130249-L-2668388 2026-10-21 (merge of deliver/Z9/Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization)
