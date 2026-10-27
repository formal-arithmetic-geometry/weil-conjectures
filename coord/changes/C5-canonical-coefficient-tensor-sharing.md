# filteredCoefficientTensorIso

## Reason

Share the existing balanced tensor construction through the explicit canonical
TensorNormalization data. The old body elaborates the full sheaf symmetry and
derived scalar presentation again, leaving too little compilation time for its
consumer proof. The new body projects the same derived isomorphism from the
canonical data, with kernel-checked conversion of the typed endpoint aliases.
The canonical data are constructed explicitly; no theorem with sorry chooses data.
No target signature or mathematical map changes.

## Old

```lean
def filteredCoefficientTensorIso (Z : Scheme.{u}) :
    filteredCoefficientExtension a Z ⋙ filteredCoefficientRestriction a Z ≅
      (derivedTensor R Z).flip.obj
        ((DerivedCategory.singleFunctor (internalModules R Z) 0).obj
          ((Mod.comap (coefficientMap a Z)).obj (Mod.regular (condensedRingObj S Z)))) := by
  letI : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    { toBraidedCategory := sheafBraidedCategory Ab.{u + 1} Z
      symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _ (sheafSymmetricCategory Z) M N }
  exact Mod.residueDerivedTensorIso (coefficientMap a Z)
```

## New

```lean
def filteredCoefficientTensorIso (Z : Scheme.{u}) :
    filteredCoefficientExtension a Z ⋙ filteredCoefficientRestriction a Z ≅
      (derivedTensor R Z).flip.obj
        ((DerivedCategory.singleFunctor (internalModules R Z) 0).obj
          ((Mod.comap (coefficientMap a Z)).obj (Mod.regular (condensedRingObj S Z)))) := by
  let e := (QuotientChange.canonicalCoefficientTensorNormalization a Z).derived
  unfold QuotientChange.D at e
  -- The kernel checks the existing scalar-functor and tensor endpoint aliases.
  run_tac Lean.Elab.Tactic.withMainContext do
    let e ← Lean.Meta.getLocalDeclFromUserName `e
    (← Lean.Elab.Tactic.getMainGoal).assign e.toExpr
    Lean.Elab.Tactic.replaceMainGoal []
```

The file adds public import Sheaf.Paper.CanonicalCoefficientTensorNormalization
because its definition now uses that module. All five original public imports stay.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientPushFilteredLegs | C5 | Same signature and canonical data; parent proof uses the shared presentation. |

`tools/downstream.py Sheaf.Paper.CoefficientPushFilteredLegs --uses
filteredCoefficientTensorIso` reports zero downstream modules and only the item
itself as a declaration user. Repository text search finds no other Lean importer or use of
filteredCoefficientTensorIso. The DAG parent route is retained; the item is not
withdrawn. There are no forced adaptations and no source-library edits.

## Status

landed 20261023T230522-L-3438591 2026-10-23 (merge of deliver/C5/Sheaf.Paper.CoefficientPushFilteredLegs)
