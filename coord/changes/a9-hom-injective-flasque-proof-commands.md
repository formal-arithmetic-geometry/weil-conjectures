# AlgebraicGeometry.isFlasque_homObj_of_coherent_injective

## Reason

Preflight treats additional `open` commands and declaration-scoped `set_option` commands
as potentially visible interface changes. They support the complete proof of flasqueness.
All existing public imports, declarations and the theorem's signature remain verbatim;
no consumer changes or target review are mathematically necessary.

## Old

```lean
open CategoryTheory
```

The theorem and namespace originally had no local elaboration options.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

The new private constructions and selected proofs have declaration-scoped options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
```

These options end after each declaration. The generic private helpers add no public API.
No notation, attribute, instance or file-level option is added. The unchanged theorem
is proved from the extension-by-zero component formula and Mathlib sheafification.
The two original private proof imports are replaced by the smaller private proof import
`WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IsFlasqueHomObjOfInjective | A9 | Complete proof; same statement and public imports. |
| Sheaf.AlgebraicGeometry.CoherentHomInjectiveAcyclic | unclaimed | Uses the identical theorem; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Transitive consumer; no adaptation needed. |
| Sheaf.Paper.ExtSheafToGlobalSpectralSequence | unclaimed | Transitive consumer; no adaptation needed. |

`tools/downstream.py ... --uses isFlasque_homObj_of_coherent_injective` lists the item
and CoherentHomInjectiveAcyclic as declaration users, and the other two as downstream
modules. No consumer file is delivered or changed.

## Status

landed 20261023T123328-L-1162305 2026-10-23 (merge of deliver/A9/Sheaf.AlgebraicGeometry.IsFlasqueHomObjOfInjective)
