# CategoryTheory.ringedHomComposition_naturality

## Reason

The proof adds a declaration-scoped namespace opening for the proved private
helper `closed_naturality`. The static interface check conservatively records
new open commands. This record documents their scope and the consumer check;
no public signature, definition, attribute or import changes.

## Old

The module-level command is:

```lean
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
```

There is no helper `closed_naturality`, and the public theorem
`CategoryTheory.ringedHomComposition_naturality` has proof `by sorry`.

## New

The module-level command remains verbatim. Immediately before the proved
private helper, the proof adds:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open MonoidalCategory in
private lemma closed_naturality
```

The namespace opening and options apply only to that private declaration.
The existing public theorem has the complete proof `by exact closed_naturality S`.
Its full signature remains identical to the existing source. Every added helper
is private and proved. The two original existence and model holes are unchanged.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RingedHomCompositionModel --uses
CategoryTheory.ringedHomComposition_naturality` lists the following downstream
module and the item's own use of the declaration. The downstream source has
been read; it needs no adaptation because the public interface is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedHomCompositionModel | C8 | Private proof helpers only; existing public types and definitions unchanged. |
| Sheaf.Paper.RingedPullbackHomEvaluationComparison | unclaimed in the current local claim records | No adaptation: its import and references retain the same interface. |

No target definition or statement changes, so no target meaning review is reopened.

## Status

landed 20261021T192923-L-764433 2026-10-21 (merge of deliver/C8/Sheaf.Algebra.Homology.RingedHomCompositionModel)
