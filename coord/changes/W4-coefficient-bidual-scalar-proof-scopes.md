# Coefficient bidual scalar descent proof scopes

## Reason

The completed `CategoryTheory.CoefficientBidual.scalar_compatibility` proof uses
categorical localization and full-subcategory shift transport. These arguments
need the same local elaboration transparency as the existing closed-category
helpers. No statement, definition, public import or attribute changes.

## Old

The original module-level elaboration settings are, verbatim:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The `scalar_compatibility` proof is `by sorry`. There is no `ScalarDescent`
section or general triangle-compatibility helper.

## New

The original module-level settings remain verbatim. The proved private general
triangle helper uses the two transparency settings locally. A new private
`ScalarDescent` section also sets both to false and opens `TensorProduct` for
its tensor formulas; this section ends before `ClosedLinearity` and `Site`.
The settings are false locally for `scalar_compatibility` as well. The
unused-variable linter is disabled for that declaration alone: its original
`hshift` and `hQ` binders are preserved verbatim, while the proof works for any
coherent shift on Q with the stated image triangles.

Private helpers compare the raw scalar category with the existing
rationalization, descend the exact transformation, and derive the triangle
and invertibility conclusions. Every new helper is fully proved. Two private
proof imports expose the rationalization-Hom and shift-whiskering APIs; twelve
unused private proof imports are removed (listed in report.md). All original
public signatures and definition bodies stay verbatim. No exported option
or instance changes, and no consumer adaptation is required.

## Users

`tools/downstream.py Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility`
and a whole-Lean-tree import/name search find no current direct consumer.
The assigned module and its DAG attachment remain in place for its planned
parents; none is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | W4 | Proof and private helpers only; public API unchanged. |

## Status

landed 20261020T233232-L-909620 2026-10-20 (merge of deliver/W4/Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility)
