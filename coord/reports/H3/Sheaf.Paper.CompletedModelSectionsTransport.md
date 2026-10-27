## What changed

Proved `transport_eq`, `transport_identity`, and `transport_tower` in
`Sheaf.Paper.CompletedModelSectionsTransport`, preserving every existing signature
and definition. The existing cochain equality is passed through localization using
the exact-functor factorization laws and the prescribed ordinary scalar counit.
This proves the integral map equality; naturality of the specified beta comparison
then proves its rational clause. The identity proof uses the existing derived
sections unit square. The tower proof inverts the existing integral sections tower
square, applies naturality at the actual intermediate map, and cancels the model
units. The rational tower follows by inverting the specified beta tower square.

Added private proof imports of `Sheaf.Paper.PointSectionsScalarExtension` with
`all`, for its existing general-field coherence lemmas, and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, for the
exact localization factorization laws. The extra instance registrations brought
in by `import all` are disabled where they conflict with the point-specific
instances. Local irreducibility keeps the coefficient limits from unfolding.
The existing `transport_eq` declaration was moved after `chainTransport_spec`,
which its proof now uses. One proved private helper records the counit/factorization
identity. The DAG node records these implementation steps without changing its dependency list.
No public import, signature, definition, target, or unit route changed.

## Proved and sorry left

Closed three of the five initial holes, in namespace
`WeilConjectures.CompletedModelSections`:

- `transport_eq`
- `transport_identity`
- `transport_tower`

Two existing holes remain, both with their original source and complete proof
plans under node `lem-pod-completed-model-sections-transport`:

- `WeilConjectures.CompletedModelSections.unit_existsUnique`
- `WeilConjectures.CompletedModelSections.derivedMap_existsUnique`

Added zero holes and split off zero statements. This is a partial proof delivery;
the remaining model-unit and realized-map construction obligations are unchanged.

## No longer needed

None. No imports, modules, declarations, or DAG nodes are withdrawn. The two
remaining obligations still require their recorded dependencies. The new proofs
use the existing point sections comparison API, so no separate import of the
more general finite-field tower package is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The previously proved cochain formula
already contains the generator computation needed for `transport_eq`; the
remaining passage to the derived category is an exact-functor factorization
calculation with the actual counit. The general-field unit, tower, and beta laws
already proved privately in `PointSectionsScalarExtension` also apply to this
module's field parameters. No new intermediate theorem is necessary for these
three holes.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
