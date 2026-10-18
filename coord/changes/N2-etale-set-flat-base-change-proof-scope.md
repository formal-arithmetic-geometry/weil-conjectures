# AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat

## Reason

The delivery's new private chart-comparison proofs use pullback notation and a local
section of implicit scheme morphisms. The static interface checker treats changes to
`open`, `section`, and `variable` commands as potentially visible changes, so records
are required even though both existing public signatures and all public imports stay
identical. No public definition or statement is repaired or weakened.

## Old

```lean
open CategoryTheory

namespace AlgebraicGeometry
```

There was no auxiliary section or shared `variable` command.

## New

```lean
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme
```

The two private exchange/pasting lemmas also use this closed lexical section:

```lean
section

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

-- Private, fully proved exchange and pullback-pasting lemmas.

end
```

Private comparison definitions carry `@[irreducible]` to prevent expensive unfolding;
their proved unit-equation API unfolds the construction explicitly only where needed.
Every added declaration is private. Existing public theorem statements and public
imports are unchanged. No target meaning changes and no target statement review reopens.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange
--uses isIso_etaleSetDegreeZeroBaseChange_of_flat` reports zero downstream modules;
the only source use is the smooth specialization in this same module. The analogous
query for the smooth specialization also has no downstream consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange | N2 | Private proof infrastructure; both original holes closed; existing signatures and visibility identical. |

No other module is adapted, and no forced adaptation is needed.

## Status

landed 20261018T071205-L-1672649 2026-10-18 (merge of deliver/N2/Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange)
