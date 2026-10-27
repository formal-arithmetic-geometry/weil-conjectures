# AlgebraicGeometry.Etale.moduleDerivedRestrictionResolution

## Reason

The proof needs transparent matching between homotopy-functor composites, derived
adjunctions and their canonical comparison maps. Two elaboration options permit those
matches in the four proved private categorical helpers. A `namespace CategoryTheory`
block contains those helpers and ends before the unchanged public declarations.
Preflight classifies the added commands as an interface change requiring this record.
No mathematical definition, public declaration signature, attribute or public import changes.

## Old

The original file has no added `CategoryTheory` namespace block or transparency options.
Its existing `set_option autoImplicit false` is preserved.

## New

```lean
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The block ends with `end CategoryTheory` before the existing
`namespace AlgebraicGeometry.Etale`. It introduces only the four fully proved private
lemmas `module_compUnit_app`, `module_leray_fac`, `module_restriction_fac` and
`module_chain`. These options govern local elaboration and export no instances,
notations or attributes. All existing public statements and abbreviations remain verbatim.

## Users

`tools/downstream.py Sheaf.TraceFormula.ModuleDerivedRestrictionResolution --uses
AlgebraicGeometry.Etale.moduleDerivedRestrictionResolution` reports the three transitive
consumers below and no external occurrence of the theorem name. None requires adaptation:
private helpers do not enter public signatures and file-local options are not imported.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactPointSourceNormalization | unclaimed | No interface change; no adaptation |
| Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules | unclaimed | No interface change; no adaptation |
| Sheaf.TraceFormula.FiniteBaseCechHypercohomology | unclaimed | No interface change; no adaptation |

## Status

landed 20261023T103437-L-3140266 2026-10-23 (merge of deliver/W8/Sheaf.TraceFormula.ModuleDerivedRestrictionResolution)
