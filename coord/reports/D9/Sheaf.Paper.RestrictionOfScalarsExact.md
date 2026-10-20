## What changed

Proved `WeilConjectures.completedIntegralRestrictScalars_exact` in
`Sheaf.Paper.RestrictionOfScalarsExact` by reusing the existing proved
`WeilConjectures.scalarReductionRestriction_exact` from
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` (a new proof-only import).
A local extensionality proof identifies its commutative-ring projection, after
forgetting commutativity, with the original completed-coefficient projection.
Rewriting that equality gives the original functor and both preservation assertions.
All public imports, definitions, theorem signatures, and docstrings are unchanged.

The imported theorem carries out the node's existing forgetful-functor argument:
the underlying abelian sheaf is unchanged; the forgetful functors preserve finite
limits and finite colimits and reflect them. Thus the unit route is unchanged.
The node already attaches this unrestricted exactness theorem, so its existing
proof, proof dependencies and Lean attachment remain correct and need no edit.
No new node or interface change is needed.

Validation: single-file server compilation through `lcompile.py` succeeded with no
warnings. Import-direction checking permits the new proof import. The proof
retains independent site, coefficient and finite-field-datum universes and covers
`n = 0` (exponent one), arbitrary schemes including empty schemes, and zero sheaves.
No flatness, surjectivity-on-sections, or new mathematical hypothesis is introduced.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.completedIntegralRestrictScalars_exact`
(blueprint node `lem-weil-restriction-of-scalars-exact`).
Holes closed: 1 of 1. Holes added: 0. Holes left in the item: 0. Split off: 0.
This is a proof from an already proved existing declaration, not a decomposition.

## No longer needed

Removed the unused proof-only imports
`Mathlib.CategoryTheory.Sites.Sheafification` and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
Their mathematical ingredients remain part of the existing unrestricted theorem's
forgetful-functor proof; no DAG dependency or module is claimed globally unreachable.
No nodes or modules are withdrawn. Public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item remains the older finite-field-datum wrapper, whereas its blueprint node's
Lean record was already moved to the proved unrestricted exactness theorem in
`DerivedScalarExtensionRestrictionAdjunction`. This makes the shortest route reuse
of that theorem, with explicit equality of the actual coefficient projections.
The old module's sorry was redundant; its statement is correct and unchanged.

Searches through `msearch.py`: LeanFinder returned the restriction definition,
additivity and forgetful limit-preservation ingredients; Loogle returned the
restriction definition, additivity and underlying-object/map formulas; grep returned
ordinary module restriction exactness. Direct `rg` of project sources found the
proved unrestricted theorem, whose full signature and proof were read. No new
lemma or duplicate declaration was introduced.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
