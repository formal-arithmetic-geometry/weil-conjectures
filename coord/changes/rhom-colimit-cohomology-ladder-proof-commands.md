# Sheaf.Paper.RHomColimitCohomologyLadder proof commands

## Reason

The static interface checker treats added `open` and local `attribute` commands as
interface changes. The proof needs the standard opposite triangulated instances
and must prevent unfolding the implementation of `homComplexFunctor` during its
identity-map calculation. These commands support the four completed proofs. All
existing public declaration signatures, definition bodies, attributes and public
imports are preserved verbatim. New helpers are private and completely proved.

## Old

The existing command was:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
```

There was no additional opposite-namespace opening or local irreducibility attribute.

## New

The existing opening remains, followed by:

```lean
open CategoryTheory.Pretriangulated.Opposite
```

Inside `namespace WeilConjectures.SfbHomFilteredColimit`, the proof also has:

```lean
attribute [local irreducible] CategoryTheory.homComplexFunctor
```

The opposite opening supplies the standard opposite triangulated structure used by
`map_distinguished_op_exact`. The local attribute is confined to elaborating this
module and changes neither the definition nor its exported attributes. Existing
public definitions and theorem statements are unchanged. Local linter suppression
on the two lemmas with unused section instances avoids changing their binders.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RHomColimitCohomologyLadder | E2 | Four proofs completed; public interfaces unchanged. |

`tools/downstream.py Sheaf.Paper.RHomColimitCohomologyLadder --uses
rhom_colimit_cohomology_ladder` reports zero downstream modules and only the item
itself as a textual use. No consumer adaptation is necessary. The unfinished
parent DAG dependencies remain attached to this node; this is not a withdrawal.

## Status

landed 20261021T134328-L-850053 2026-10-21 (merge of deliver/E2/Sheaf.Paper.RHomColimitCohomologyLadder)
