## What changed

Retired `Sheaf.AlgebraicGeometry.RationalFunctions`, the depth-zero SUPERSET retirement
item, in favor of `WeilConjectures.AlgebraicGeometry.RationalFunctions`.
`Sheaf.AlgebraicGeometry.RationalFunctionRing`, its sole direct consumer, now publicly
re-exports the upstream module instead of duplicating `Scheme.rationalFunctionRing`.
Redirected the `lean` record of `def-sc-rational-functions` to that existing upstream
construction. No upstream file or target statement was edited.

Read Stacks Morphisms, section Rational maps, definitions 01RS/01RT/01RU and proof of
01RV. Dense opens, intersection, inclusion, section diagram and colimit agree literally
with the upstream construction, at arbitrary scheme universes and including the empty
scheme. The upstream twin additionally has the proved cofilteredness instance.

Validation: server-only `lcompile.py --all` compiled the changed wrapper (1.5 s) and its
sole transitive consumer `Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks` (4.0 s),
without warnings or errors. The consumer was copied only for verification and is
unchanged; it is not delivered. The change record is
`coord/changes/retire-rational-functions-T1.md`.

## Proved and sorry left

Zero holes in the assigned module before retirement, zero remaining, zero added, zero
split off. No holed theorem is claimed proved. All four dense-open constructions and
the partial-order instance now come from the existing upstream implementation;
the rational-function colimit comes from its same-named upstream definition.
The already proved `Scheme.rationalFunctions_generic_stalks` compiles unchanged.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.RationalFunctions`.
Removed import: `Sheaf.AlgebraicGeometry.RationalFunctions` from
`Sheaf.AlgebraicGeometry.RationalFunctionRing`; replaced by the official upstream twin.
Removed the duplicate definition of `Scheme.rationalFunctionRing` from its compatibility
wrapper. The wrapper remains available to its existing generic-stalk consumer.
No mathematical DAG node or proof dependency is pruned. No new nodes.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief describes a module with holes, but the assigned item is
a zero-hole retirement repair explicitly listed in `coord/retire-items.tsv`.
The 2026-10-11 node attachment predated the upstream universe-polymorphic colimit ring;
the stated reason for a separate Sheaf construction no longer applies.

Searches: `msearch.py` leanfinder returned Mathlib's irreducible-scheme function-field
API, which does not replace this general-scheme colimit. Loogle did not know the
project-local declaration, and its Mathlib grep returned no match. Direct `rg` and
full reads of the project modules identified the exact upstream construction and all
consumers. No proof route or unit realization changes.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
