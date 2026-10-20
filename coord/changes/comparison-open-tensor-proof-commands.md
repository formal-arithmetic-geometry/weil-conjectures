# Sheaf.SixFunctors.ComparisonOpenTensorCoherence: proof commands

## Reason

The stage-3 preflight flags the command-level diff introduced by the private
categorical proof helpers. This record documents that diff for the independent
reader. No existing declaration changes type, visibility, or universes. The two
public definition bodies are byte-identical to the baseline. No target meaning
changes and no target statement review is reopened.

## Old

The original command skeleton after the imports and module docstring was:

```lean
@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
```

The rest of that namespace contained the two public definitions and the theorem.
There were no local helper namespaces or elaborator options.

## New

The original public-section, universe, and outer opens are retained. Private
categorical helper declarations now precede the public definitions, in this scope:

```lean
namespace CategoryTheory

open _root_.CategoryTheory.Functor
```

This namespace is closed before `namespace AlgebraicGeometry.ProEtale` is opened.
The existing public declarations remain in their original namespace. Every added
helper is private. Individual helper declarations use the following scoped
elaboration controls where needed:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
```

The commands are scoped to their individual declarations; the combinations differ
between helpers. Diagnostic elaboration bounds of 10000, 15000, 20000 and 50000
heartbeats are also scoped to individual helpers, below the normal default.
There is no new notation, attribute on a public declaration, or public instance.
The public theorem now has its completed proof. The proof-only import change is
recorded in report.md. The only semantic change is eliminating its original hole.

## Users

`tools/downstream.py Sheaf.SixFunctors.ComparisonOpenTensorCoherence --uses
comparison_open_tensor_coherence` listed the following two downstream modules;
neither contains a textual use of that theorem. The same command lists only the
item module as a use. Both public definitions and all public types are unchanged,
so these consumers need no adaptation and no statement becomes weaker or stronger.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ComparisonOpenTensorCoherence | U6 | Its original theorem is proved; only private helpers and scoped proof commands are added. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in queue snapshot | Direct importer; public API unchanged, no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in queue snapshot | Transitive importer; public API unchanged, no adaptation. |

## Status

landed 20261020T131156-L-1253591 2026-10-20 (merge of deliver/U6/Sheaf.SixFunctors.ComparisonOpenTensorCoherence)
