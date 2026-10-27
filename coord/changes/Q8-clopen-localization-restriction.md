# AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.restriction

## Reason

Repeated eager expansion of the restriction functor and the nested gluing witnesses made the full localization proof expensive to elaborate. Keep precisely the same functor body and type, but use a semireducible definition. A local irreducibility attribute inside the proof module controls elaboration; importers receive the ordinary definition.

## Old

```lean
abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    Modules.{t, u, v, w} R ⥤ Modules.{t, u, v, w} ((clopenRingRestriction j).obj R) :=
  clopenModuleRestriction j R
```

## New

```lean
def restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    Modules.{t, u, v, w} R ⥤ Modules.{t, u, v, w} ((clopenRingRestriction j).obj R) :=
  clopenModuleRestriction j R
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization | Q8 | Proofs use the packaged normalization and explicit insertion. |
| Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor | P8 | Existing consumer checked unchanged against the repaired definitions. |
| Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent | P9 | Existing consumer checked unchanged against the repaired definitions. |
| Sheaf.Paper.ClopenCompletedOperationTowers | Q5 | Existing consumer checked unchanged against the repaired definitions. |
| Sheaf.SixFunctors.ClopenCompositeCounitNormalization | unclaimed | Existing consumer checked unchanged against the repaired definitions. |

## Status

landed 20261024T190732-L-43719 2026-10-24 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization)
