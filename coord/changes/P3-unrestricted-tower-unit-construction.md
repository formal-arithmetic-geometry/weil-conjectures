# WeilConjectures.unrestrictedTowerUnit

## Reason

Construct the normalized chain-level unit directly from the ordinary scalar-extension
adjunction. The old definition selected the unique family from an existence-and-uniqueness
proof. Component calculations involving that choice unfolded completed coefficient rings
and their limit cones and exceeded 200000 heartbeats. The explicit degreewise construction
makes the component formula and chain-map naturality check directly.

Both definitions have the same signature and send each section x to the sheafification
of 1 tensor x. The existing uniqueness theorem determines exactly this family, so the
mathematical object is unchanged. `unrestrictedTowerUnit_condition` records the formula and
`unrestrictedTowerUnit_eq_chosen` proves equality with the former chosen family.
No target signature is changed. This definition lies below the targets, so their semantic
review is reopened with the same uniquely specified unit and no changed hypotheses or
conclusions.

## Old

```lean
noncomputable def unrestrictedTowerUnit
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    P ⟶ unrestrictedTowerComplex l E Y n P :=
  (unrestrictedTowerMaps_existUnique l E Y P).exists.choose n
```

## New

```lean
noncomputable def unrestrictedTowerUnit
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    P ⟶ unrestrictedTowerComplex l E Y n P :=
  { f := fun i ↦ (scalarReductionExtension_adjunction l E Y n).choose.unit.app (P.X i)
    comm' := fun i j _ ↦
      ((scalarReductionExtension_adjunction l E Y n).choose.unit.naturality
        (P.d i j)).symm }
```

## Users

`tools/downstream.py Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
--uses unrestrictedTowerUnit` found these three declaration users. The remaining transitive
importers do not themselves mention the changed declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted | P3 | Same normalized unit; prove all three original holes and expose its formula. |
| Sheaf.Paper.IntegralReductionTowerCanonical | unclaimed | Replace the proof that the unit has its formula by `unrestrictedTowerUnit_condition`; all signatures stay identical. |
| Sheaf.Paper.IsomorphismReductionTower | B2 | Its statements use the same normalized unit and keep their meaning; no source change. |

## Status

landed 20261019T093532-L-2323649 2026-10-19 (merge of deliver/P3/Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted)
