# AlgebraicGeometry.Etale.AffineLineNormalizedDescent.normalized_descent

## Reason

Preflight attempt 32728 requires a change record for the added local attributes and
scope command. They control elaboration of the new private proofs. All existing
signatures, definition bodies, declaration attributes and public imports stay verbatim.
No source-library module changes.

## Old

There are no local attribute commands between the original `open scoped` command and
namespace, and no additional scope opening after `sheaf_rigidity`:

```lean
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.AffineLineNormalizedDescent
```

## New

The module adds these commands for its own elaboration:

```lean
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
```

After `sheaf_rigidity`, it opens the notation used in the private proofs:

```lean
open scoped AlgebraicGeometry.Etale
```

The attributes are local and the scope opening changes parsing in this file. They do
not export a new instance or alter any existing public declaration. Every existing
signature and definition body was checked verbatim against the shared source.

## Users

`tools/downstream.py` reports zero downstream modules and only the item itself as a
textual user of `normalized_descent`. The unfinished DAG parent still needs this node;
it is preserved, with its interface unchanged. No consumer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent | M4 | Local proof elaboration only; all existing interfaces unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | F2 | Unfinished DAG parent; preserved interface, no adaptation. |

## Status

landed 20261023T231835-L-3650574 2026-10-23 (merge of deliver/M4/Sheaf.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent)
