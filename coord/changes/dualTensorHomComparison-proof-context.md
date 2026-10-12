# AlgebraicGeometry.Scheme.Modules.dualTensorHom_eq_ihomUnitTensorToIhom

## Reason

The static interface checker conservatively treats added `section`, `variable`, `open`,
`local notation`, and `attribute [local instance]` commands as interface changes. They support
three fully proved private helpers for this comparison. Every added notation, instance, universe,
and namespace opening is confined to the helper section or namespace. The two elaboration options
are scoped with `in` to the helper declarations. No public statement, definition, import, instance,
or elaboration attribute changes. This record documents the context commands required by preflight;
it does not request or conceal a mathematical statement change.

## Old

```lean
theorem dualTensorHom_eq_ihomUnitTensorToIhom {X : Scheme.{u}} (M N : X.Modules) :
    dualTensorHom M N = MonoidalClosed.ihomUnitTensorToIhom M N
```

The proof was `by sorry`. The file's context was `universe u`, `open CategoryTheory`, and
`namespace AlgebraicGeometry.Scheme.Modules`, with the existing public section and import.

## New

```lean
theorem dualTensorHom_eq_ihomUnitTensorToIhom {X : Scheme.{u}} (M N : X.Modules) :
    dualTensorHom M N = MonoidalClosed.ihomUnitTensorToIhom M N
```

The target applies the fully proved private site-level comparison. The original global context is
preserved. An additional section contains universe `v`, `open MonoidalCategory`, a section of
monoidal-category variables for the private pairing calculation, and namespace `SheafOfModules`.
That namespace locally declares notation for the ring sheaf, sheafification functor and adjunction;
locally enables the existing monoidal, symmetric and closed instances; and binds the site hypotheses
needed by the private adjunction transport and comparison proofs. Both namespace and outer section
end before the original target declaration. The maxHeartbeats and transparency options use `in`
and affect only individual private helper proofs.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DualTensorHomComparison --uses
 dualTensorHom_eq_ihomUnitTensorToIhom` found 287 downstream modules; only the following downstream
module mentions the target declaration. The source module itself is the owned item K3. Because the
public signature and all public definitions, imports, instances and attributes are unchanged, the
meaning of every downstream statement is unchanged. Private helper context does not escape its
section. No module is adapted and no target statement requires renewed definition review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeDualPairing | unclaimed | Same theorem with identical type; its existing rewrite remains valid. No adaptation. |

## Status

landed 20261012T202242-L-705482 2026-10-12 (merge of deliver/K3/Sheaf.AlgebraicGeometry.DualTensorHomComparison)
