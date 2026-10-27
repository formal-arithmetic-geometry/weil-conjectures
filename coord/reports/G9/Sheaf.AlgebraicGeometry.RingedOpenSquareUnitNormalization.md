## What changed

Proved `AlgebraicGeometry.Scheme.RingedRestrictionExchange.actual_open_square_alpha_normalization`
in `Sheaf.AlgebraicGeometry.RingedOpenSquareUnitNormalization`. All existing public
signatures, definitions, docstrings and imports are unchanged.

Added proved private helpers for compositor units, equality transport of
coefficient-decorated arrows, and sectionwise pasting. These adapt the already
proved private square-unit argument in `RingedOrdinaryOpenExchange`; no dependency
on that module is added. The final theorem specializes the general square-unit
formula to `actualSquare p j R`.

The private bridge `actual_normalization_of_formula` translates the general unit
formula into `AlphaNormalization` while its square isomorphism is still a variable.
Only afterwards is the selected `exchangeModuleSquare` inserted. This prevents the
kernel from unfolding its large body during predicate conversion. The complete
proof compiled through `lcompile.py` in 19.8 seconds. Temporary profiling and
inspection commands were removed before delivery.

Updated the item's DAG proof and proof origin to describe these actual Lean steps.
The strict-tower and open-restriction data dependencies and the blueprint unit route
are retained. The aggregate site-morphism composition theorem is not used.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.actual_open_square_alpha_normalization`
(node `lem-sf-ringed-open-square-unit-normalization`).
Added 0 holes; 0 holes remain in the item. Every new private helper has a complete proof.
No split-off statements or new modules are added.

## No longer needed

Both existing public imports are needed by the statements and actual coefficient
construction, so no imports are removed. Removed the unused proof dependency
`lem-weil-pbc-site-morphism-composition` (module
`WeilConjectures.CategoryTheory.SiteMorphismComposition`): the argument uses the
specified module compositor normalization and Mathlib adjunction-unit identities
directly, with no application of that aggregate site-composition theorem. This
removes only the item's proof dependency; no library module is withdrawn.
No import of ordinary exchange, derived exchange, resolutions, or a sectionwise
beta comparison is required by the new proof.

## Where the brief, the DAG or earlier work was wrong

The brief's mathematical plan is valid. The existing private square-unit argument
in `RingedOrdinaryOpenExchange` already implements its essential calculation,
although it is not exposed as a reusable public theorem. Its proved pasting
helpers can be adapted locally, avoiding another decomposition and any interface
changes to that shared module. Directly converting the selected square's unit
formula exceeded the kernel checking limit; translating the predicates for an
arbitrary square isomorphism first makes the same argument compile quickly.
Empty schemes and zero coefficient rings require no extra hypothesis, since only
categorical isomorphisms and unit identities are used.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
