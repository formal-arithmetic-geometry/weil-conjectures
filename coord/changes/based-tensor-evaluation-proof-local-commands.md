# SheafOfModules.basedTensorProductSections

## Reason

The completed proof uses local irreducibility attributes to keep the finite-product
limit and coordinate constructions from expanding during elaboration. The static
consumer check classifies the added commands as a visible command change. This record
covers those commands, private local notation, and scoped proof/linter options. No
public declaration signature or public definition body changes.

## Old

```lean
def basedTensorProductSections (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ M).val.obj U ≅
      ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) :=
  PreservesProduct.iso
    (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
      (fun _ : Fin d ↦ M) ≪≫ ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)
```

There were no local irreducibility attributes for the product-evaluation definition,
`CategoryTheory.Limits.limit`, or `SheafOfModules.changeOfRingsMap` in this file.

## New

The public definition above stays verbatim, including its type and body. The added
commands are local to this module:

```lean
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] basedTensorProductSections changeOfRingsMap
```

The private coordinate definitions have `@[irreducible]`; their proved coordinate APIs
are used explicitly. Private local notation abbreviates the ring sheaf and ring map.
The theorem's existing scoped heartbeat setting is lowered from 800000 to 200000.
A scoped `linter.unusedVariables false` preserves the original binder names `b` and `he`.
These commands add no exported instance or attribute. The main theorem is filled with a
complete proof and keeps its original signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation | Y5 | Local proof elaboration only; both public signatures and the definition body stay identical. |

`tools/downstream.py Sheaf.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation
--uses basedTensorProductSections` reports zero downstream modules and only this module
as a user of the definition. No consumer adaptation is needed. DAG parents may still use
the proved theorem; its unchanged interface serves them.

## Status

landed 20261023T152140-L-455141 2026-10-23 (merge of deliver/Y5/Sheaf.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation)
