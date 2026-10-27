# Private localization proof section

## Reason

The proof uses generic private localization helpers to avoid expanding the concrete
sheaf category in naturality and triangle calculations. The static command comparison
flags the added section and its variables. Their scope ends before the existing public
variables; no existing public declaration acquires any parameter or changed instance.
The scoped heartbeat option affects elaboration of one proof only.

## Old

No localization helper section or local variables preceded the existing scheme variables.
All existing public signatures and definition bodies are retained verbatim.

## New

```lean
section Localization

variable {C D : Type*} [Category C] [Category D]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
  (T S : C ⥤ C) (F G : D ⥤ D)
  (cF : Q ⋙ F ≅ T ⋙ Q) (cG : Q ⋙ G ≅ S ⋙ Q)
-- private, fully proved helpers
end Localization
```

Before the main theorem:

```lean
set_option maxHeartbeats 300000 in
-- The concrete sheaf instance conversions in this assembly exceed the default budget.
```

## Users

`tools/downstream.py` reports the transitive import closure. No public statement or
definition changes, so none of its 496 modules needs adaptation. Qualified interface
search finds one direct consumer of this module's public tensor interface:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LineUnboundedDerivedTensor | W9 | private proof helpers only |
| Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison | unclaimed | none; signatures and data unchanged |

No source-library file is modified; no target meaning changes.

## Status

landed 20261024T021953-L-2885575 2026-10-24 (merge of deliver/W9/Sheaf.Algebra.Homology.LineUnboundedDerivedTensor)
