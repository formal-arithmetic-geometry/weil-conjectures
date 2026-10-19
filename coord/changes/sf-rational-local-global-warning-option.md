# sfRationalLocalGlobalPowerTorsion warning option

## Reason

Repair of the return at head `da50058855`: the landing hole census interpreted the
`sorry` component of `set_option warn.sorry false` as an unattributed hole. Remove
the warning suppression. The module now contains no hole tokens and needs no
suppression. Preflight classifies removal of this command as an interface change
and requires this record.

No existing declaration, signature, instance, visibility, definition or public import
changes. Warning behavior is diagnostic only: this command does not change the
meaning of any declaration or target. The completed theorem proof is retained.

## Old

```lean
@[expose] public section
set_option autoImplicit false
set_option warn.sorry false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

## New

```lean
@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

## Users

`tools/downstream.py Sheaf.Paper.SfRationalLocalGlobalPowerTorsion
--uses sfRationalLocalGlobalPowerTorsion` lists the three downstream modules below;
the only textual occurrence of the declaration is its own defining module.
None requires adaptation: no elaborated declaration or imported interface changes.
Resumed verification on 2026-10-20: the item compiles successfully with the
option removed (27.2 seconds), with exit code 0 and no warnings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | C7 | Remove warning suppression; prove theorem. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | None; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | None; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | None; no adaptation. |

## Status

landed 20261019T231058-L-546040 2026-10-19 (merge of deliver/C7/Sheaf.Paper.SfRationalLocalGlobalPowerTorsion)
