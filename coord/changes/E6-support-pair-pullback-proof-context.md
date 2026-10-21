# SupportQuotientPairPullback proof elaboration context

## Reason

The proof introduces private adjunction calculations and stalk arguments. Their section
variables, universe declarations, `omit` commands and elaboration settings are proof
infrastructure. This record exposes those command changes for independent review. No
existing declaration signature, definition body, visibility, or public import changes.

## Old

The original common elaboration context was:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
```

After `supportQuotientEtaleConstantGerm`, the original file proceeded directly to the
docstring and statement of `supportQuotient_pair_pullback`, whose body was `by sorry`.

## New

The original common context is unchanged. Between the final existing definition and the
existing theorem, the proof adds private helpers in `ConstantSections` and `Construction`
sections, with explicit universes and variables. These settings allow the category and
adjunction interfaces to unfold during proof elaboration:

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Some private declarations use `omit [Finite A] in` to state the helper without an unused
assumption. All new definitions and lemmas are private and fully proved. None occurs in
an existing public signature or public definition body. The theorem's complete original
signature and the bodies of every existing definition remain verbatim. These settings
are local to elaboration of this module and do not change importing modules.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SupportQuotientPairPullback --uses
AlgebraicGeometry.Scheme.supportQuotient_pair_pullback` reports zero current Lean importers
and only the declaration's own module as a textual user. Unfinished DAG parents retain
the same interface and dependency; no module or node is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportQuotientPairPullback | E6 | Proof and private helpers only; existing interface unchanged. |

## Status

landed 20261021T152309-L-1853157 2026-10-21 (merge of deliver/E6/Sheaf.AlgebraicGeometry.SupportQuotientPairPullback)
