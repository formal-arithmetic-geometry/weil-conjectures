# GlobalHomAdjunctionIso proof helper elaboration

## Reason

The static stage-3 checker treats the scoped `omit` commands of the two new
private proved helpers as a change to what importing modules see. This record
makes that diagnostic explicit. No existing declaration signature, visibility,
public import, definition, target meaning, universe, or section variable changes.
No other module needs adaptation. The four scoped transparency settings avoid
expensive unfolding during existing proofs while keeping their proof statements.

## Old

The module's global elaboration settings, unchanged by this delivery, are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The two private helpers and their scoped `omit` commands did not exist.
The existing `internalHomMate_exists`, `tensorAdjunctionCore`, `lerayCore`, and
`schemeGlobalHomAdjunctionMap_isIso` declarations had no scoped overriding options.
`exists_schemeHomTensorPullbackIso` had its existing signature and proof `by sorry`.

## New

Each of the four existing helper/proof declarations named above is scoped by:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

Each new private theorem is preceded by:

```lean
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
```

Their signatures are:

```lean
private theorem pullbackTensorModelMap_isIso (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) : IsIso (pullbackTensorModelMap X P N)

private theorem pullbackCounit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) :
    IsIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
```

Both helpers are proved. Neither is used in any public signature or the body of
any public definition. The public existence theorem now has a complete proof,
with its original ModuleCat derived-category binder retained. It is preceded by:

```lean
set_option linter.unusedSectionVars false in
```

This suppresses only the warning about retaining that existing binder, rather
than silently removing it. These scoped commands do not survive their respective
declarations. All public signatures and definitions remain identical.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | V2 | Private proof helpers and scoped elaboration only; unchanged existing signatures and definitions. |

The new helpers are private and have no downstream users. No dependency interface
was modified, and no forced adaptation was made.

## Status

landed 20261013T002358-L-2377058 2026-10-13 (merge of deliver/V2/Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso)
