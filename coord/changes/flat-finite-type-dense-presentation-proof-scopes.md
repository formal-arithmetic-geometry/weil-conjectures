# AlgebraicGeometry.flat_finite_type_dense_presentation

## Reason

The proved private helpers and the final proof use names from `TopologicalSpace` and
`AlgebraicGeometry.Scheme.Modules`. The new affine restriction helper also needs a scoped
elaboration option. Preflight conservatively classifies changed top-level commands as an
interface change, so this record documents them. No public signature, public import,
attribute, instance, or definition is changed.

## Old

The original name-resolution commands were:

```lean
open CategoryTheory
open AlgebraicGeometry
```

The original module had no scoped `backward.isDefEq.respectTransparency` command.

## New

The commands used by the private helpers and theorem proof are:

```lean
open CategoryTheory
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
```

The private theorem `finitePresentation_sections_of_restrict` is preceded by:

```lean
set_option backward.isDefEq.respectTransparency false in
```

This option is restricted to that private theorem. These commands affect name resolution and
elaboration within this file. All existing public signatures and public imports stay identical.

The returned delivery also removes the file-level `set_option warn.sorry false` command.
It only suppressed warnings and is unnecessary for elaboration; removing it avoids the
landing scanner treating its option name as an unattributed hole. No declaration changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | E4 | Private helpers and the theorem proof elaborate using the new open namespaces; the public statement is unchanged. |

`tools/downstream.py Sheaf.TraceFormula.FlatFiniteTypeDensePresentation --uses
flat_finite_type_dense_presentation` lists 48 downstream modules and no downstream textual
users of the declaration (only its own declaration). None needs adaptation: no signature,
instance, public import, notation, or attribute changed, and these namespace opens do not
propagate to importers.

## Status

landed 20261023T131536-L-2119163 2026-10-23 (merge of deliver/E4/Sheaf.TraceFormula.FlatFiniteTypeDensePresentation)
