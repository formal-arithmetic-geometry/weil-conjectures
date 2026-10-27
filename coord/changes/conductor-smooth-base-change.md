# conductor_smooth_base_change proof elaboration options

## Reason

The completed proof uses the existing categorical pullback and pushforward APIs,
whose coercions require the same backward definitional equality transparency settings
used by their source module. The proof therefore adds file-local environment options
within this module. The repair also removes the unnecessary file-local warning
suppression command: the source hole ledger matches the `sorry` component of
`warn.sorry` and reported it as an unattributed hole before the first declaration.
Removing that command leaves warning configuration to the compile environment and
removes the reported token without changing a proof. The preflight classifies the changed command list as an
interface change; this record documents that syntactic classification. No declaration
signature, definition, theorem statement, public import, or runtime behavior changes.

## Old

The module had no file-level transparency options:

```
set_option autoImplicit false
set_option warn.sorry false
```

## New

The module retains `set_option autoImplicit false`, removes
`set_option warn.sorry false`, and adds:

```
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The transparency options affect elaboration only; removing warning suppression
affects diagnostics only. These changes add no axioms and alter no declaration.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.TraceFormula.ConductorSmoothBaseChange | G9 | The item proof elaborates with the required categorical coercion transparency. |

`tools/downstream.py ... --uses conductor_smooth_base_change` reports only this
module as using the declaration. There are 36 modules in the transitive import
closure. No public definition, statement or public import is changed, so no
consumer signature or proof needs adaptation. The two direct importers are
`Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches` and
`Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization`; neither
mentions the theorem.

## Status

landed 20261023T131545-L-2121582 2026-10-23 (merge of deliver/G9/Sheaf.TraceFormula.ConductorSmoothBaseChange)
