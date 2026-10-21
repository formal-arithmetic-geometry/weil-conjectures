# Sheaf.Paper.CompatibleCoefficientTower: private proof context

## Reason

The completed tensor-tower proof uses private constructions, proved private instances,
and transparency settings to control unfolding of module structures and sheafification.
Preflight conservatively flags the added attribute commands and instance registrations.
This record documents them. Existing public signatures, definitions, and public imports
remain verbatim unchanged; no target or definition changes meaning.

## Old

The original module has the command:

```lean
set_option autoImplicit false
```

It has no private helpers, instance registrations, or local irreducibility attributes.
The original body of `SheafOfModules.exists_compatibleCoefficientTower` is:

```lean
  sorry
```

## New

After the existing public definitions the proof environment adds:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
```

These options control this module's elaboration and are not exported to importers.
Individual private declarations additionally use the scoped forms of these options.
The only added attribute commands are:

```lean
attribute [local irreducible] coefficientSheafificationComparison
attribute [local irreducible] tensorCoefficientSection
```

Both refer to new private constructions, after their underlying-map and pure-tensor
formulas have been proved. They control unfolding in the remaining proofs.

The three added private instance signatures are:

```lean
private instance tensorPreFunctor_additive (a : R ⟶ S) :
    (tensorPreFunctor a).Additive

private instance coefficientSheafificationComparison_isIso
    {A D : Sheaf J RingCat.{u}} (a : A ⟶ D) (P : PresheafOfModules.{u} D.obj) :
    IsIso (coefficientSheafificationComparison a P)

private instance towerFunctor_additive
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) :
    (towerFunctor r p b hr hp).Additive
```

Each is completely proved. Their types concern only the new private functors or
comparison map. They add no instance for an existing public construction. The public
existence theorem packages the constructed functor and its proved properties; its
signature is unchanged and no public definition refers to a private helper.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompatibleCoefficientTower | N2 | Its proof uses the private context above. |

`tools/downstream.py Sheaf.Paper.CompatibleCoefficientTower --uses
SheafOfModules.exists_compatibleCoefficientTower` reports zero downstream modules
and only this module's own declaration as a textual use. A search of both library
roots confirms no direct importer or external textual use. No consumer needs adaptation.
The assigned node and its planned parent dependencies remain in place.

## Status

landed 20261021T111401-L-96320 2026-10-21 (merge of deliver/N2/Sheaf.Paper.CompatibleCoefficientTower)
