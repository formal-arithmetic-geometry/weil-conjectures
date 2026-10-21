# Roos transition proof scopes

## Reason

The first preflight requests a change record for the commands added around the
private proof helpers in `Sheaf.CategoryTheory.RoosTransitionHomotopy`. This record
accounts for those commands. No mathematical definition or statement is repaired.

## Old

The module had its public definitions and a single unproved theorem, with no generic
product-calculation section or generic cone-calculation section.

## New

The public definitions, theorem signature, attributes and public imports are identical.
The original theorem is now proved. All new declarations are proved private helpers.

The new `Products` section binds a generic preadditive category, a tower and its
product. Its `variable` and `omit` commands parameterize only the private helpers;
the section ends before the original category is used again. The new `Cone` section
opens `CochainComplex` and `CochainComplex.HomComplex`, omits the unused countable
product instance and binds four generic complexes. It also ends before the tower
comparison maps are constructed. The earlier `restricted_asFunctor` helper has an
`omit` command removing its unused product instance. No notation, attribute,
instance or public declaration is introduced by these scopes.

The added `set_option backward.defeqAttrib.useBackward true` controls elaboration
of the proofs in this file. It changes no existing declaration type or body.
The original transparency settings remain in place.

## Users

`tools/downstream.py Sheaf.CategoryTheory.RoosTransitionHomotopy --uses
CategoryTheory.RoosTransition.roos_transition_homotopy
CategoryTheory.RoosTransition.TransitionHomotopy` reports zero downstream Lean
modules. A source search also found no current Lean importer. No consumer needs
adaptation, and no other module is changed.

The DAG parent `lem-weil-specified-pullback-comparison-alpha` (Lean module
`Sheaf.Paper.SpecifiedPullbackComparisonAlpha`) still needs this item. Its expected
statement and all the definitions it uses remain identical. Its route and dependency
record are retained. Every target statement and every definition used by a target is
unchanged; this proof does not reopen the target-statement review.

## Status

landed 20261021T130010-L-2485323 2026-10-21 (merge of deliver/E4/Sheaf.CategoryTheory.RoosTransitionHomotopy)
compiled without warnings, and the theorem's axiom check returned only `propext`,
`Classical.choice` and `Quot.sound`. No module held by another group is adapted.
