# AlgebraicGeometry.Etale.finite_range_exchange_comparison: private proof context

## Reason

The existing theorem is proved using generic private exact-couple helpers. The
static interface checker flags the added namespace/universe/variable commands,
even though the new variable context is confined to those private helpers and
closed before the existing theorem. This record documents the commands and
all downstream modules. It introduces no mathematical interface change.

## Old

The existing header context before the theorem namespace was:

```lean
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TruncationExchange
open CategoryTheory.BigradedExactCouple

namespace AlgebraicGeometry.Etale
```

## New

After the same `open` commands, the following context is added for proved private
helpers, then closed before `namespace AlgebraicGeometry.Etale`:

```lean
universe v w

namespace CategoryTheory.BigradedExactCouple

variable {C : Type v} [Category.{w} C] [Abelian C]
```

The helpers are all `private theorem`s, with complete proofs. Two helpers omit
the unused ambient `[Abelian C]` assumption locally. The namespace is ended
before the existing public theorem. Its complete signature and all definitions
are unchanged. Import removals are documented separately in
`finite-range-comparison-import-pruning.md`; the added private context itself
changes no import visibility.

## Users

Rechecked against the current shared repository on 2026-10-16 using
`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FiniteRangeComparison --uses
AlgebraicGeometry.Etale.finite_range_exchange_comparison`:
zero downstream modules; the only occurrence of the theorem is its declaration
in the item itself. The earlier list of five importers predates the upstream
sync and is superseded by this source-graph check.

| module | group holding it | effect |
|---|---|---|

No downstream adaptation is required. No target statement or definition changes.
This module is currently outside the targets' import closure, so closing its
hole does not claim a decrease in that closure's sorry count.

## Status

landed 20261016T075723-L-1295295 2026-10-16 (merge of deliver/C3/Sheaf.AlgebraicGeometry.FiniteRangeComparison)
