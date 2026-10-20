# AlgebraicGeometry.ProEtale.SemilinearProperOpen.J

## Reason

Keep this derived functor as a named def with explicit source and target. The abbrev caused elaboration and typeclass search in naturality and mate expressions to expand the localization functor construction. The body is unchanged; only default unfolding and the explicit type presentation change. All theorem statements and geometric constructions keep their meaning.

## Old

```lean
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (extension C τ j).mapDerivedCategory
```

## New

```lean
def J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Derived C τ U ⥤ Derived C τ X :=
  (extension C τ j).mapDerivedCategory
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | S4 | Compiles the same constructions and theorem signatures with the new proofs. |

| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed (quarantined) | Uses `J`; unchanged body and functor type; no adaptation. |

The live-only downstream search reports no users beyond the item. The archived
`Sheaf.Paper.FiniteFreeCompactComposition` also directly imports the item and uses
`J`; it is retained below. The DAG parents and definition attachments are
retained. No consumer needs adaptation: the body is unchanged, and the sources,
targets, theorem signatures and public imports keep the same meaning.

## Status

landed 20261020T230833-L-618817 2026-10-20 (merge of deliver/S4/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
