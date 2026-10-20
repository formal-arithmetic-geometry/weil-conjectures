# Coefficient bidual linearity proof scopes

## Reason

The proof of `CategoryTheory.CoefficientBidual.subcategory_linearity` uses generic
closed-category and central tensor-unit calculations. Its private helpers need the
monoidal notation and the same elaboration transparency used by other closed-category
proofs in this library. The delivery checker records additional commands even when
they are section-local, so this record documents their scope and consumers.

## Old

The item has four theorem holes and no `ClosedLinearity` section.

## New

A `ClosedLinearity` section contains three fully proved private lemmas. Within that
section only, `MonoidalCategory` is opened and
`backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` are false. The section ends before the
original `Site` section. No option is exported to a consumer. A fourth proved private
helper specializes the generic result to the recorded ringed-site bidual.

The original `subcategory_linearity` signature includes an additive instance binder
which `Functor.Linear` does not depend on explicitly. Its completed proof triggers
the unused-variable linter, so that linter is disabled for this declaration alone.
The original binder name and entire signature stay verbatim.

Two private proof imports are added:
`Mathlib.CategoryTheory.Monoidal.Linear` and
`Mathlib.CategoryTheory.Monoidal.Limits.Preserves`.
All original public imports, public signatures and definition bodies stay verbatim.
No other module or target changes.

## Users

A search of current Lean sources for imports of
`Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility` finds no direct consumer.
Only the assigned item is changed. The DAG still retains its future dependencies and
unit route; the module is not withdrawn. There is no public API change and no consumer
adaptation is needed. The complete item and its delivery axiom probe compile cleanly.

## Status

landed 20261020T230803-L-612389 2026-10-20 (merge of deliver/K3/Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility)
