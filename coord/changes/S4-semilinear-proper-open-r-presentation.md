# AlgebraicGeometry.ProEtale.SemilinearProperOpen.R

## Reason

Keep this derived functor as a named def with explicit source and target. The abbrev caused elaboration and typeclass search in naturality and mate expressions to expand the localization functor construction. The body is unchanged; only default unfolding and the explicit type presentation change. All theorem statements and geometric constructions keep their meaning.

## Old

```lean
abbrev R {X Y : Scheme.{u}} (f : X ⟶ Y) := (push C τ f).rightDerivedFunctor
```

## New

```lean
def R {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ X ⥤ Derived C τ Y :=
  (push C τ f).rightDerivedFunctor
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | S4 | Compiles the same constructions and theorem signatures with the new proofs. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |

The live-only downstream search omits the quarantined consumers listed above.
They are retained conservatively from the landing check's name matches, which
include unrelated unqualified names. Inspection of the archived sources found no
required adaptation: the changed definitions have definitionally equal bodies
and the existing theorem signatures and public imports are unchanged. In
particular, `FiniteFreeCompactComposition` directly imports the item and uses its
system functors; those constructions keep the same sources, targets and bodies.
The DAG parents and definition attachments are retained. No archived source is
withdrawn or restored by this delivery; this presentation repair does not change
a target's meaning.

## Status

landed 20261020T230833-L-618817 2026-10-20 (merge of deliver/S4/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
