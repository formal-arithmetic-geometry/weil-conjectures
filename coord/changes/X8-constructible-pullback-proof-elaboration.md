# ConstructiblePullbackTExact proof elaboration

## Reason

Two existing theorem proofs now use generic proved private helpers. The file adds a
local section of variables for those helpers and enables backward definitional equality.
The private shift-additivity theorem is registered only with `[local instance]`.
No existing public signature, definition, visibility or instance attribute changes.
The change record documents commands conservatively identified by preflight as an
interface change. No target meaning changes and no consumer adaptation is required.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The two delivered theorems had whole-proof `sorry` bodies; there were no private helpers.

## New

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem module_shift_additive (E : Type u) [Field E] :
    ∀ n : ℤ, (shiftFunctor (DerivedCategory (ModuleCat.{u} E)) n).Additive := by
  intro n
  infer_instance

attribute [local instance] module_shift_additive
```

The section `Composite` scopes the generic helper variables and is closed before all
existing public declarations. Three private theorems prove cohomology composition,
heart composition and degree-zero homology vanishing. No helper is used in any public
signature or definition body. The only public uses occur inside the two theorem proofs.

## Users

`tools/downstream.py Sheaf.Paper.ConstructiblePullbackTExact --uses module_shift_additive`
reports 43 downstream modules and zero users of the private helper. Direct importers:

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Unchanged signatures and public imports; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | D3 | Unchanged signatures and public imports; no adaptation. |

All transitive consumers see identical existing declarations and public imports.
No module other than the assigned item is modified.

## Status

landed 20261021T144027-L-38308 2026-10-21 (merge of deliver/X8/Sheaf.Paper.ConstructiblePullbackTExact)
